-- Prove2me | Definitions.Def_ModularCurve_X1PrimitiveSpecialization
-- name    : ModularCurve_X1PrimitiveSpecialization
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/7de35b0c-743d-5c9d-8994-50d0356313ef
-- title:
--   Norm-free part of J1​(M0​qc) and Igusa specialisation data
-- statement:
--   Fix naturals $M_0,q,c$ and write $M=M_0q^c$. The finite set `primitiveReps M₀ q c` consists of the $d<M$ that are coprime to $M$ and satisfy $d\equiv 1 \pmod{M_0q^{c-1}}$ (truncated subtraction in the exponent), i.e. representatives in $[0,M)$ of the kernel of $(\mathbb Z/M)^\times\to(\mathbb Z/M_0q^{c-1})^\times$; `mem_primitiveReps` records this membership criterion. For a finite set $S\subseteq\mathbb N$, `normFreeEnd M S` is the additive endomorphism $x\mapsto |S|\,x-\sum_{d\in S}\langle d\rangle x$ of `JOne M`, where $\langle d\rangle$ is `diamondOneBar M d`, the $\mathbb Z$-linear endomorphism given by the semilinear action of the base change to $\overline{\mathbb Q}$ of the chosen diamond automorphism of the $q$-expansion function field of $X_1(M)$. The additive subgroup `primitivePart M₀ q c` of `JOne M` is the image of `normFreeEnd M (primitiveReps M₀ q c)`; two helper lemmas identify its elements and note that values of that endomorphism lie in it.
--
--   The structure `X1PrimitiveSpecialization M₀ q c P k π`, for a valuation subring $P$ of $\overline{\mathbb Q}$, a field $k$ and a ring homomorphism $\pi:P\to k$, packages specialisation data as fields: a family `igusaDiamond` of $k$-algebra automorphisms of `x1FunctionFieldC k M`, indexed by $d\in\mathbb N$, together with the requirement that they are compatible with `diamondAutBar M d` under coefficientwise reduction of Laurent series along $\pi$; two additive maps `spInf`, `spZero` from `primitivePart M₀ q c` to `JOneC M k`; invariance of `spInf` under the inertia subgroup of $P$ over $\mathbb Q$; equivariance of `spInf` for $\langle d\rangle$ against the semilinear automorphism induced by `igusaDiamond d`; invariance of `spZero` under the composites $\langle u\rangle\circ\sigma$ for $\sigma$ in inertia and $u\equiv 1\pmod{M_0}$ acting on $q^c$-th roots of unity by $\zeta\mapsto\zeta^u$; and, as a final field, the assertion that for every prime $p\neq q$ an element of the $p$-adic Tate module of `JOne M` all of whose components lie in `primitivePart M₀ q c` vanishes as soon as `spInf` and `spZero` kill all of them.
--
--   **Relation to Mathlib.** Mathlib has no Jacobians of modular curves, diamond operators or Igusa specialisation; these are the project's own notions, built on Mathlib's valuation subrings and their inertia subgroups, Hahn/Laurent series, and `Finset` constructions.
--
--   **Where it is used.** The norm-free (primitive) part isolates the part of $J_1(M_0q^c)$ on which the nebentypus has exact conductor $q^c$ at $q$, and a term of `X1PrimitiveSpecialization` encodes the two specialisation maps at the cusps $\infty$ and $0$ of the Igusa description of the reduction at $q$, together with their inertia- and diamond-equivariance and their joint injectivity on Tate modules. This is the form in which the $q$-adic geometry enters the level-lowering step at $q$ for the mod $p$ representation attached to the Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_X1PrimitiveSpecialization.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_X1Diamond
import Definitions.Def_EllipticCurve_TateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open HahnSeries IntermediateField AlgebraicCurve CongruenceSubgroup

namespace ModularCurve

section NormFree

def primitiveReps (M₀ q c : ℕ) : Finset ℕ :=
  (Finset.range (M₀ * q ^ c)).filter
    (fun d => Nat.Coprime d (M₀ * q ^ c) ∧ d ≡ 1 [MOD M₀ * q ^ (c - 1)])

theorem mem_primitiveReps {M₀ q c d : ℕ} :
    d ∈ primitiveReps M₀ q c ↔
      d < M₀ * q ^ c ∧ Nat.Coprime d (M₀ * q ^ c) ∧ d ≡ 1 [MOD M₀ * q ^ (c - 1)] := by
  rw [primitiveReps, Finset.mem_filter, Finset.mem_range]

variable (M : ℕ)

def normFreeEnd (S : Finset ℕ) : JOne M →+ JOne M where
  toFun x := S.card • x - ∑ d ∈ S, diamondOneBar M d x
  map_zero' := by simp
  map_add' x y := by
    rw [nsmul_add, Finset.sum_congr rfl fun d _ => map_add (diamondOneBar M d) x y,
      Finset.sum_add_distrib]
    abel

@[simp]
theorem normFreeEnd_apply (S : Finset ℕ) (x : JOne M) :
    normFreeEnd M S x = S.card • x - ∑ d ∈ S, diamondOneBar M d x :=
  rfl

def primitivePart (M₀ q c : ℕ) : AddSubgroup (JOne (M₀ * q ^ c)) :=
  (normFreeEnd (M₀ * q ^ c) (primitiveReps M₀ q c)).range

theorem mem_primitivePart {M₀ q c : ℕ} {y : JOne (M₀ * q ^ c)} :
    y ∈ primitivePart M₀ q c ↔ ∃ x, normFreeEnd (M₀ * q ^ c) (primitiveReps M₀ q c) x = y :=
  AddMonoidHom.mem_range

theorem normFreeEnd_mem_primitivePart {M₀ q c : ℕ} (x : JOne (M₀ * q ^ c)) :
    normFreeEnd (M₀ * q ^ c) (primitiveReps M₀ q c) x ∈ primitivePart M₀ q c :=
  ⟨x, rfl⟩

end NormFree

section Datum

variable (M₀ q c : ℕ) (P : ValuationSubring (AlgebraicClosure ℚ))
variable (k : Type) [Field k] (π : P →+* k)

structure X1PrimitiveSpecialization where

  igusaDiamond : ℕ → (x1FunctionFieldC k (M₀ * q ^ c) ≃ₐ[k] x1FunctionFieldC k (M₀ * q ^ c))

  igusaDiamond_apply_eq : ∀ (d : ℕ) (y y' : LaurentSeries P)
    (hy : coeffMap P.subtype y ∈ x1FunctionFieldBar (M₀ * q ^ c))
    (hy' : coeffMap P.subtype y' ∈ x1FunctionFieldBar (M₀ * q ^ c)),
    diamondAutBar (M₀ * q ^ c) d ⟨coeffMap P.subtype y, hy⟩ = ⟨coeffMap P.subtype y', hy'⟩ →
      ∀ (hk : coeffMap π y ∈ x1FunctionFieldC k (M₀ * q ^ c))
        (hk' : coeffMap π y' ∈ x1FunctionFieldC k (M₀ * q ^ c)),
        igusaDiamond d ⟨coeffMap π y, hk⟩ = ⟨coeffMap π y', hk'⟩

  spInf : primitivePart M₀ q c →+ JOneC (M₀ * q ^ c) k

  spZero : primitivePart M₀ q c →+ JOneC (M₀ * q ^ c) k

  spInf_smul : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ (y : primitivePart M₀ q c)
    (h : σ • (y : JOne (M₀ * q ^ c)) ∈ primitivePart M₀ q c), spInf ⟨_, h⟩ = spInf y

  spInf_diamondOneBar : ∀ (d : ℕ) (y : primitivePart M₀ q c)
    (h : diamondOneBar (M₀ * q ^ c) d (y : JOne (M₀ * q ^ c)) ∈ primitivePart M₀ q c),
    spInf ⟨_, h⟩ = SemilinearAut.ofAlgAut (igusaDiamond d) • spInf y

  spZero_diamondOneBar_smul : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ u : ℕ, u ≡ 1 [MOD M₀] →
    (∀ ζ : AlgebraicClosure ℚ, ζ ^ (q ^ c) = 1 → σ ζ = ζ ^ u) →
      ∀ (y : primitivePart M₀ q c)
        (h : diamondOneBar (M₀ * q ^ c) u (σ • (y : JOne (M₀ * q ^ c))) ∈ primitivePart M₀ q c),
        spZero ⟨_, h⟩ = spZero y

  eq_zero_of_forall_eq_zero : ∀ (p : ℕ) [Fact p.Prime], p ≠ q →
    ∀ (y : TateModule p (JOne (M₀ * q ^ c)))
      (h : ∀ n, (y : ℕ → JOne (M₀ * q ^ c)) n ∈ primitivePart M₀ q c),
      (∀ n, spInf ⟨_, h n⟩ = 0) → (∀ n, spZero ⟨_, h n⟩ = 0) → y = 0

end Datum

end ModularCurve

end


