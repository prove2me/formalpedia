-- Prove2me | Definitions.Def_ModularCurve_X1PrimitiveSpecializationAtP
-- name    : ModularCurve_X1PrimitiveSpecializationAtP
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:29.330635+00:00
-- url     : https://prove2.me/theorems/f9157988-52f0-509f-8360-9270ba4dbd7d
-- title:
--   Specialisation data at p for the norm-free part of J1​(M)
-- statement:
--   Fix $M$ and a prime $p$. `normFreeRepsAt M p` is the finite set of $d < M$ with $\gcd(d,M)=1$ and $d \equiv 1 \pmod{M/p}$ (natural-number division), i.e. a set of representatives for the kernel of $(\mathbb Z/M)^\times \to (\mathbb Z/(M/p))^\times$; `mem_normFreeRepsAt` records this membership criterion. Applying to this set the endomorphism $x \mapsto |S|\,x - \sum_{d \in S}\langle d\rangle x$ of `JOne M` given by `normFreeEnd` (with $\langle d\rangle$ the diamond endomorphism `diamondOneBar M d`), `normFreePartAt M p` is defined as the image subgroup, the norm-free part; `mem_normFreePartAt` and `normFreeEnd_mem_normFreePartAt` are the evident membership facts.
--
--   For a prime $p$, a valuation subring $P$ of $\overline{\mathbb Q}$ and a field $k$ of characteristic $p$, the structure `X1PrimitiveSpecializationAtP M p P k` packages two additive maps $\mathrm{sp}_\infty, \mathrm{sp}_0$ from `normFreePartAt M p` to $\mathrm{Pic}^0$ of the characteristic-$p$ $q$-expansion function field `qExpFunctionFieldC k (Gamma1 M)` over $k$, together with properties carried as fields: $\mathrm{sp}_\infty$ is invariant under the inertia subgroup of $P$ over $\mathbb Q$; the vanishing locus of $\mathrm{sp}_0$ is stable under the decomposition subgroup; for $\sigma$ with `P.IsFrobeniusAt σ p` (so $\sigma$ lies in the decomposition group and acts as $x \mapsto x^p$ on the residue field), $\mathrm{sp}_\infty(\sigma y) = \mathrm{Fr}_*(\mathrm{sp}_\infty y)$ via `qExpFrobeniusPushforwardModL`; on $\ker \mathrm{sp}_0$ the Hecke operator `heckeOperatorOneBar M ⟨p, _⟩` satisfies $\mathrm{sp}_\infty(U_p y) = \mathrm{Fr}^*(\mathrm{sp}_\infty y)$ via `qExpFrobeniusPullbackModL` and $\mathrm{sp}_0(U_p y)=0$. Two further fields concern the $p$-adic Tate module [`TateModule p (JOne M)`](../def/EllipticCurve_TateModule.html#L15) (sequences $(x_n)$ with $p^n x_n = 0$, $p x_{n+1} = x_n$) of elements all of whose coordinates lie in the norm-free part: $U_p$-surjectivity up to $\mathrm{sp}_0$, and the assertion that if $\mathrm{sp}_\infty$ and $\mathrm{sp}_0$ kill every coordinate of $x$ then $m x$, for some $m \neq 0$, lies in the $\mathbb Z_p$-span of the elements $\tau y - y$ with $\tau$ in inertia fixing all $p$-th roots of unity and $y$ again having all coordinates in the norm-free part. Thus the structure is a hypothesis-bundling datum: the classical reduction theory at $p$ is assumed in the form of these maps and identities rather than constructed.
--
--   **Relation to Mathlib.** Mathlib has no modular curves, Hecke or diamond operators, nor any Igusa-curve specialisation theory; `normFreeEnd`, `JOne`, `Pic0`, the $q$-expansion function fields and [`TateModule`](../def/EllipticCurve_TateModule.html#L15) are the project's own notions. The inertia and decomposition subgroups used in the conditions are built from Mathlib's valuation-theoretic ramification subgroups of a `ValuationSubring`.
--
--   **Where it is used.** The norm-free part isolates the part of $J_1(M)$ on which the nebentypus is ramified at $p$, and a specialisation datum of this kind is the input used in lowering the level at the residue characteristic, where the reduction of $X_1(M)$ at $p$ is described by Igusa curves and the two cusps $\infty$ and $0$ give two specialisation maps exchanged by $U_p$ and Frobenius. It feeds the level-lowering step of the Frey–Serre–Ribet argument, whose conclusion is the nonexistence of the Galois representation attached to a Frey curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_X1PrimitiveSpecializationAtP.lean

import Mathlib
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_ModularCurve_X1PrimitiveSpecialization
import Definitions.Def_ModularCurve_QExpFrobeniusModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

open IntermediateField AlgebraicCurve CongruenceSubgroup

namespace ModularCurve

section NormFree

variable (M p : ℕ)

def normFreeRepsAt : Finset ℕ :=
  (Finset.range M).filter (fun d => Nat.Coprime d M ∧ d ≡ 1 [MOD M / p])

variable {M p} in
theorem mem_normFreeRepsAt {d : ℕ} :
    d ∈ normFreeRepsAt M p ↔ d < M ∧ Nat.Coprime d M ∧ d ≡ 1 [MOD M / p] := by
  rw [normFreeRepsAt, Finset.mem_filter, Finset.mem_range]

def normFreePartAt : AddSubgroup (JOne M) :=
  (normFreeEnd M (normFreeRepsAt M p)).range

variable {M p} in
theorem mem_normFreePartAt {y : JOne M} :
    y ∈ normFreePartAt M p ↔ ∃ x, normFreeEnd M (normFreeRepsAt M p) x = y :=
  AddMonoidHom.mem_range

theorem normFreeEnd_mem_normFreePartAt (x : JOne M) :
    normFreeEnd M (normFreeRepsAt M p) x ∈ normFreePartAt M p :=
  ⟨x, rfl⟩

end NormFree

section Datum

variable (M p : ℕ) [Fact p.Prime] (P : ValuationSubring (AlgebraicClosure ℚ))
variable (k : Type) [Field k] [CharP k p]

structure X1PrimitiveSpecializationAtP where

  spInf : normFreePartAt M p →+ Pic0 k (qExpFunctionFieldC k (Gamma1 M))

  spZero : normFreePartAt M p →+ Pic0 k (qExpFunctionFieldC k (Gamma1 M))

  spInf_smul_of_mem_inertia : ∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ (y : normFreePartAt M p)
    (h : σ • (y : JOne M) ∈ normFreePartAt M p), spInf ⟨_, h⟩ = spInf y

  spZero_smul_eq_zero : ∀ σ ∈ P.decompositionSubgroup ℚ, ∀ (y : normFreePartAt M p)
    (h : σ • (y : JOne M) ∈ normFreePartAt M p), spZero y = 0 → spZero ⟨_, h⟩ = 0

  spInf_smul_of_isFrobeniusAt : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
    P.IsFrobeniusAt σ p → ∀ (y : normFreePartAt M p) (h : σ • (y : JOne M) ∈ normFreePartAt M p),
      spInf ⟨_, h⟩ = qExpFrobeniusPushforwardModL k (Gamma1 M) p (spInf y)

  spInf_hecke_of_spZero_eq_zero : ∀ (y : normFreePartAt M p)
    (h : heckeOperatorOneBar M ⟨p, Fact.out⟩ (y : JOne M) ∈ normFreePartAt M p),
    spZero y = 0 → spInf ⟨_, h⟩ = qExpFrobeniusPullbackModL k (Gamma1 M) p (spInf y)

  spZero_hecke_eq_zero : ∀ (y : normFreePartAt M p)
    (h : heckeOperatorOneBar M ⟨p, Fact.out⟩ (y : JOne M) ∈ normFreePartAt M p),
    spZero y = 0 → spZero ⟨_, h⟩ = 0

  exists_spZero_hecke_eq : ∀ (x : TateModule p (JOne M))
    (hx : ∀ n, (x : ℕ → JOne M) n ∈ normFreePartAt M p),
    ∃ x' : TateModule p (JOne M), (∀ n, (x' : ℕ → JOne M) n ∈ normFreePartAt M p) ∧
      ∀ (n : ℕ) (h : heckeOperatorOneBar M ⟨p, Fact.out⟩ ((x' : ℕ → JOne M) n) ∈ normFreePartAt M p),
        spZero ⟨_, h⟩ = spZero ⟨_, hx n⟩

  exists_smul_mem_span_of_forall_eq_zero : ∀ (x : TateModule p (JOne M))
    (hx : ∀ n, (x : ℕ → JOne M) n ∈ normFreePartAt M p),
    (∀ n, spInf ⟨_, hx n⟩ = 0) → (∀ n, spZero ⟨_, hx n⟩ = 0) →
      ∃ m : ℕ, m ≠ 0 ∧ ((m : ℤ_[p]) • x) ∈ Submodule.span ℤ_[p]
        {z : TateModule p (JOne M) |
          ∃ τ ∈ P.inertiaSubgroupIn ℚ, (∀ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 → τ ζ = ζ) ∧
            ∃ y : TateModule p (JOne M), (∀ n, (y : ℕ → JOne M) n ∈ normFreePartAt M p) ∧
              z = TateModule.rep p (JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) τ y - y}

end Datum

end ModularCurve

end


