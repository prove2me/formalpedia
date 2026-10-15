-- Prove2me | Definitions.Def_OAI_Algebra_BogomolovPop_Kummer
-- name    : OAI_Algebra_BogomolovPop_Kummer
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T20:24:00.401508+00:00
-- url     : https://prove2.me/theorems/8eaa6c87-f609-4438-8051-bcc40cd67aac
-- title:
--   Tate module of roots of unity and Kummer characters on the abelian pro-$\ell$ Galois group
-- statement:
--   Throughout, $F$ is a field with a fixed algebraic closure $\bar F$, $G_F=\operatorname{Aut}_F(\bar F)$ is its absolute Galois group with the Krull topology, and $\mu_n(\bar F)=\{z\in\bar F^\times : z^n=1\}$ is the group of $n$-th roots of unity, always equipped with the discrete topology. For a prime $\ell$ and $a\in\mathbb Z_\ell$, $a_e\in\{0,\dots,\ell^e-1\}$ denotes the residue of $a$ modulo $\ell^e$. The module sets up the roots of unity of $\ell$-power order and the Kummer characters, and pushes the latter down to the abelian pro-$\ell$ Galois group.
--
--   1. **Tate module.** For $\ell,e\in\mathbb N$ the transition homomorphism $\mu_{\ell^{e+1}}(\bar F)\to\mu_{\ell^e}(\bar F)$ is $z\mapsto z^\ell$, and the Tate module of roots of unity is the subgroup
--   $$
--   T_\ell(F)=\Big\{(z_e)_{e\ge0}\in\prod_{e\ge0}\mu_{\ell^e}(\bar F)\ :\ z_{e+1}^{\,\ell}=z_e\ \text{for all }e\Big\}=\varprojlim_e\mu_{\ell^e}(\bar F).
--   $$
--
--   2. **Primitive levels.** For a field $A$, the set of primitive $\ell^e$-th roots of unity in $A$; and, for $\ell>0$ and $e\le n$, the map sending a primitive $\ell^n$-th root of unity $z$ to the primitive $\ell^e$-th root of unity $z^{\ell^{\,n-e}}$.
--
--   3. **Cyclic coordinates.** For a primitive $n$-th root of unity $z\in A$ with $n\neq0$, the group isomorphism $\mathbb Z/n\mathbb Z\cong\mu_n(A)$, $i\mapsto z^i$. Accompanying lemmas record its compatibility with the levels: if $z$ and $w$ are primitive roots of unity of orders $\ell^e$ and $\ell^{e+1}$ with $w^\ell=z$, then $(w^i)^\ell=z^{\bar i}$, where $\bar i$ is the reduction of $i\in\mathbb Z/\ell^{e+1}\mathbb Z$ modulo $\ell^e$.
--
--   4. **$\ell$-adic coordinates on the Tate module.** For a prime $\ell$ and a compatible system $(z_e)_{e\ge0}$ of primitive $\ell^e$-th roots of unity in $\bar F$ (that is, $z_{e+1}^{\,\ell}=z_e$ for all $e$), the homomorphism from the additive group of $\ell$-adic integers
--   $$
--   \mathbb Z_\ell\to T_\ell(F),\qquad a\mapsto\big(z_e^{\,a_e}\big)_{e\ge0}.
--   $$
--
--   5. **Kummer roots and Kummer characters.** From here on an algebraically closed field $k$ together with a homomorphism $k\to F$ is fixed. (Two auxiliary facts are recorded: every root of unity in a field extension of $k$ lies in the image of $k$, and consequently every element of $G_F$ fixes every root of unity in $\bar F$.) For $n>0$ and $f\in F^\times$ let $\sqrt[n]{f}\in\bar F^\times$ be a chosen $n$-th root of $f$. The Kummer character of $f$ is the group homomorphism
--   $$
--   \kappa_{f,n}:G_F\to\mu_n(\bar F),\qquad \kappa_{f,n}(\sigma)=\frac{\sigma\big(\sqrt[n]{f}\big)}{\sqrt[n]{f}} .
--   $$
--   It does not depend on the chosen root (every $r\in\bar F^\times$ with $r^n=f$ gives the same value $\sigma(r)/r$); its kernel is the stabilizer of $\sqrt[n]{f}$, which is open, so $\kappa_{f,n}$ is continuous; and $f\mapsto\kappa_{f,n}$ is a group homomorphism $F^\times\to\operatorname{Hom}(G_F,\mu_n(\bar F))$, the Kummer pairing.
--
--   6. **Descent to the abelian pro-$\ell$ group.** Let $\mathcal G_F(\ell)$ be the maximal pro-$\ell$ quotient of $G_F$ (the quotient by the intersection of all open normal subgroups $H$ such that $G_F/H$ is an $\ell$-group), let $\Pi^a_\ell(F)$ be the quotient of $\mathcal G_F(\ell)$ by the closure of its commutator subgroup, and let $\pi_F:G_F\to\Pi^a_\ell(F)$ be the projection. For $\ell>0$ and $n=\ell^e$ the character $\kappa_{f,\ell^e}$ factors first through $\mathcal G_F(\ell)$ (its image is an $\ell$-group) and then through $\Pi^a_\ell(F)$ (its target is abelian and discrete). This gives continuous homomorphisms
--   $$
--   \bar\kappa_{f,e}:\Pi^a_\ell(F)\to\mu_{\ell^e}(\bar F),\qquad \bar\kappa_{f,e}\big(\pi_F(\sigma)\big)=\kappa_{f,\ell^e}(\sigma)\quad(\sigma\in G_F).
--   $$
--
--   7. **Kummer pairing on $\Pi^a_\ell(F)$.** The group homomorphism $F^\times\to\operatorname{Hom}\big(\Pi^a_\ell(F),\mu_{\ell^e}(\bar F)\big)$, $f\mapsto\bar\kappa_{f,e}$; in particular $\bar\kappa_{fg,e}=\bar\kappa_{f,e}\,\bar\kappa_{g,e}$.
--
--   These objects connect the Galois group $\Pi^a_\ell(F)$ with the multiplicative group of $F$: through the Kummer pairing, classes in $F^\times/(F^\times)^{\ell^e}$ become characters of $\Pi^a_\ell(F)$, and the Tate module makes it possible to describe the action of a field automorphism on all roots of unity of $\ell$-power order by a single $\ell$-adic scalar.
--
--   **Formalization Note** $G_F$ is `AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F`; the root $\sqrt[n]{f}$ is `kummerRoot n hn f`, picked by the axiom of choice, and $\kappa_{f,n}$, $\bar\kappa_{f,e}$ are `kummerCharacter`, `kummerPiA`. The Kummer objects take the algebraically closed field `k` as an implicit argument with `[Algebra k F]`. The discrete topology on `rootsOfUnity n (AlgebraicClosure F)` is installed as a global instance, and in `padicToTate` the additive group $\mathbb Z_\ell$ appears as `Multiplicative (PadicInt ℓ)`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/BogomolovPop/Kummer.lean

-- Generated from openai/math@1581d4c lean/OAI/Algebra/BogomolovPop/Kummer.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BogomolovPopInjectivity mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BogomolovPopInjectivity
import Definitions.Def_OAI_Algebra_BogomolovPop_Foundations
import Definitions.Def_OAI_Algebra_BogomolovPop_Canonical
import Definitions.Def_OAI_Algebra_BogomolovPop_PowerCompletion

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

/-! Tate bases, Kummer characters and scalar conjugation. -/

noncomputable section
open scoped Topology

noncomputable section
namespace BogomolovPop
open scoped Topology
instance finiteRootsTopology (n : ℕ) (F : Type*) [Field F] :
    TopologicalSpace (rootsOfUnity n (AlgebraicClosure F)) := ⊥
instance finiteRootsDiscrete (n : ℕ) (F : Type*) [Field F] :
    DiscreteTopology (rootsOfUnity n (AlgebraicClosure F)) := ⟨rfl⟩

variable {F : Type*} [Field F]
def rootTransition (ell e : ℕ) :
    rootsOfUnity (ell ^ (e + 1)) (AlgebraicClosure F) →*
      rootsOfUnity (ell ^ e) (AlgebraicClosure F) where
  toFun z := ⟨(z : (AlgebraicClosure F)ˣ) ^ ell, by
    rw [mem_rootsOfUnity, ← pow_mul, ← pow_succ']
    exact (mem_rootsOfUnity _ _).mp z.property⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [mul_pow]

def tateModuleGroup (ell : ℕ) (F : Type*) [Field F] :
    Subgroup (∀ e : ℕ, rootsOfUnity (ell ^ e) (AlgebraicClosure F)) where
  carrier := {z | ∀ e, rootTransition ell e (z (e + 1)) = z e}
  one_mem' := fun e => map_one _
  mul_mem' := by intro x y hx hy e; rw [Pi.mul_apply, map_mul, hx, hy]; rfl
  inv_mem' := by intro x hx e; rw [Pi.inv_apply, map_inv, hx]; rfl

abbrev TateModule (ell : ℕ) (F : Type*) [Field F] := tateModuleGroup ell F

end BogomolovPop
noncomputable section
namespace BogomolovPop
variable {A : Type*} [Field A]

abbrev PrimitiveLevel (ell e : ℕ) :=
  {z : rootsOfUnity (ell ^ e) A // IsPrimitiveRoot (z : Aˣ) (ell ^ e)}

def primitiveDown (ell : ℕ) (hell : 0 < ell) (e n : ℕ) (h : e ≤ n)
    (z : PrimitiveLevel (A := A) ell n) : PrimitiveLevel (A := A) ell e := by
  have hp : IsPrimitiveRoot ((z.val : Aˣ) ^ (ell ^ (n-e))) (ell ^ e) :=
    z.property.pow (pow_pos hell n) (by rw [← pow_add, Nat.sub_add_cancel h])
  exact ⟨⟨_, hp.pow_eq_one⟩, hp⟩

def zmodRootEquiv {n : ℕ} [NeZero n] {z : Aˣ} (hz : IsPrimitiveRoot z n) :
    Multiplicative (ZMod n) ≃* rootsOfUnity n A :=
  hz.zmodEquivZPowers.toMultiplicative.trans
    ((MulEquiv.multiplicativeAdditive (Subgroup.zpowers z)).trans
      (MulEquiv.subgroupCongr hz.zpowers_eq))

lemma zmodRootEquiv_nat {n : ℕ} [NeZero n] {z : Aˣ} (hz : IsPrimitiveRoot z n) (i : ℕ) :
    (zmodRootEquiv hz (Multiplicative.ofAdd (i : ZMod n)) : Aˣ) = z ^ i := by
  change (hz.zmodEquivZPowers (i : ZMod n)).toMul.val = _
  rw [hz.zmodEquivZPowers_apply_coe_nat]
  rfl

lemma zmodRootEquiv_val {n : ℕ} [NeZero n] {z : Aˣ} (hz : IsPrimitiveRoot z n) (i : ZMod n) :
    (zmodRootEquiv hz (Multiplicative.ofAdd i) : Aˣ) = z ^ i.val := by
  simpa using zmodRootEquiv_nat hz i.val

lemma zmodRootEquiv_transition (ell e : ℕ) (hell : 0 < ell) {z w : Aˣ}
    (hz : IsPrimitiveRoot z (ell ^ e)) (hw : IsPrimitiveRoot w (ell ^ (e+1)))
    (hc : w ^ ell = z) (i : ZMod (ell ^ (e+1))) :
    letI : NeZero (ell ^ e) := ⟨pow_ne_zero _ hell.ne'⟩
    letI : NeZero (ell ^ (e+1)) := ⟨pow_ne_zero _ hell.ne'⟩
    (zmodRootEquiv hw (Multiplicative.ofAdd i) : Aˣ) ^ ell =
      (zmodRootEquiv hz (Multiplicative.ofAdd
        ((ZMod.castHom (pow_dvd_pow ell (Nat.le_succ e)) (ZMod (ell^e))) i)) : Aˣ) := by
  let : NeZero (ell ^ e) := ⟨pow_ne_zero _ hell.ne'⟩
  let : NeZero (ell ^ (e+1)) := ⟨pow_ne_zero _ hell.ne'⟩
  have hi : (ZMod.castHom (pow_dvd_pow ell (Nat.le_succ e)) (ZMod (ell^e))) i =
      (i.val : ZMod (ell^e)) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val i, map_natCast]
  rw [zmodRootEquiv_val, hi, zmodRootEquiv_nat]
  rw [← pow_mul, mul_comm i.val ell, pow_mul, hc]

end BogomolovPop

namespace BogomolovPop
open scoped Topology
open Filter

variable {ell : ℕ} [Fact ell.Prime]

end BogomolovPop

namespace BogomolovPop
variable {F : Type*} [Field F] {ell : ℕ} [Fact ell.Prime]

def padicToTate (z : ℕ → (AlgebraicClosure F)ˣ)
    (hz : ∀ e, IsPrimitiveRoot (z e) (ell ^ e))
    (hc : ∀ e, z (e+1) ^ ell = z e) :
    Multiplicative (PadicInt ell) →* TateModule ell F where
  toFun a := ⟨fun e => zmodRootEquiv (hz e) (Multiplicative.ofAdd (PadicInt.toZModPow e a.toAdd)),
    fun e => Subtype.ext (by
      change _ ^ ell = _
      rw [zmodRootEquiv_transition ell e (Nat.Prime.pos Fact.out) (hz e) (hz (e+1)) (hc e)]
      congr 2
      exact DFunLike.congr_fun (PadicInt.zmod_cast_comp_toZModPow e (e+1) (Nat.le_succ e)) a.toAdd)⟩
  map_one' := by
    apply Subtype.ext
    funext e
    simp
  map_mul' a b := by
    apply Subtype.ext
    funext e
    simp [map_add]

end BogomolovPop

namespace BogomolovPop
end BogomolovPop

noncomputable section
namespace BogomolovPop

open Polynomial

theorem torsion_is_constant {k A : Type*} [Field k] [IsAlgClosed k] [Field A]
    [Algebra k A] {n : ℕ} (hn : 0 < n) {x : A} (hx : x ^ n = 1) :
    x ∈ Set.range (algebraMap k A) := by
  have hm : x ∈ algebraicClosure k A := mem_algebraicClosure_iff.mpr
    (IsAlgebraic.of_pow hn (hx ▸ isAlgebraic_one))
  rw [IntermediateField.eq_bot_of_isAlgClosed_of_isAlgebraic (algebraicClosure k A)] at hm
  exact hm

variable {k F : Type*} [Field k] [IsAlgClosed k] [Field F] [Algebra k F]

include k in

theorem galois_fixes_torsion {n : ℕ} (hn : 0 < n)
    (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) {x : AlgebraicClosure F} (hx : x ^ n = 1) :
    σ x = x := by
  obtain ⟨c, rfl⟩ := torsion_is_constant (k := k) hn hx
  rw [IsScalarTower.algebraMap_apply k F (AlgebraicClosure F), σ.commutes]

def kummerRoot (n : ℕ) (hn : 0 < n) (f : Fˣ) : (AlgebraicClosure F)ˣ :=
  Units.mk0 (IsAlgClosed.exists_pow_nat_eq (algebraMap F (AlgebraicClosure F) (f : F)) hn).choose
    (by
      intro he
      have h := (IsAlgClosed.exists_pow_nat_eq
        (algebraMap F (AlgebraicClosure F) (f : F)) hn).choose_spec
      rw [he, zero_pow hn.ne'] at h
      exact f.ne_zero ((algebraMap F (AlgebraicClosure F)).injective (by simpa using h.symm)))

theorem kummerRoot_pow (n : ℕ) (hn : 0 < n) (f : Fˣ) :
    (kummerRoot n hn f : AlgebraicClosure F) ^ n =
      algebraMap F (AlgebraicClosure F) (f : F) :=
  (IsAlgClosed.exists_pow_nat_eq _ hn).choose_spec

def kummerRatio (n : ℕ) (hn : 0 < n) (f : Fˣ) (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) :
    rootsOfUnity n (AlgebraicClosure F) :=
  ⟨Units.map σ.toMonoidHom (kummerRoot n hn f) / kummerRoot n hn f, by
    rw [mem_rootsOfUnity]
    apply Units.ext
    change (σ (kummerRoot n hn f : AlgebraicClosure F) /
      (kummerRoot n hn f : AlgebraicClosure F)) ^ n = 1
    rw [div_pow, ← map_pow, kummerRoot_pow, σ.commutes,
      div_self ((_root_.map_ne_zero _).mpr f.ne_zero)]⟩

include k in

theorem ratio_eq_of_pow_eq {n : ℕ} (hn : 0 < n)
    (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)
    (r s : (AlgebraicClosure F)ˣ) (hrs : (r : AlgebraicClosure F) ^ n = (s : AlgebraicClosure F) ^ n) :
    σ (r : AlgebraicClosure F) / (r : AlgebraicClosure F) =
      σ (s : AlgebraicClosure F) / (s : AlgebraicClosure F) := by
  have hh := galois_fixes_torsion (k := k) hn σ (x := (r : AlgebraicClosure F) / s) (by
    rw [div_pow, hrs, div_self (pow_ne_zero _ s.ne_zero)])
  rw [map_div₀, div_eq_div_iff ((_root_.map_ne_zero σ).mpr s.ne_zero) s.ne_zero] at hh
  apply (div_eq_div_iff r.ne_zero s.ne_zero).mpr
  simpa [mul_comm] using hh

include k in

def kummerCharacter (n : ℕ) (hn : 0 < n) (f : Fˣ) :
    (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) →* rootsOfUnity n (AlgebraicClosure F) where
  toFun := kummerRatio n hn f
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    simp [kummerRatio]
  map_mul' σ τ := by
    apply Subtype.ext
    apply Units.ext
    change σ (τ (kummerRoot n hn f : AlgebraicClosure F)) / kummerRoot n hn f =
      (σ (kummerRoot n hn f : AlgebraicClosure F) / kummerRoot n hn f) *
        (τ (kummerRoot n hn f : AlgebraicClosure F) / kummerRoot n hn f)
    have hh := galois_fixes_torsion (k := k) hn σ
      (x := τ (kummerRoot n hn f : AlgebraicClosure F) / kummerRoot n hn f) (by
        rw [div_pow, ← map_pow, kummerRoot_pow, τ.commutes,
          div_self ((_root_.map_ne_zero _).mpr f.ne_zero)])
    rw [map_div₀] at hh
    have hs0 := (_root_.map_ne_zero σ).mpr (kummerRoot n hn f).ne_zero
    rw [(div_eq_iff hs0).mp hh]
    ring

theorem kummerCharacter_apply_of_root (n : ℕ) (hn : 0 < n) (f : Fˣ)
    (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) (r : (AlgebraicClosure F)ˣ)
    (hr : (r : AlgebraicClosure F) ^ n = algebraMap F (AlgebraicClosure F) (f : F)) :
    ((kummerCharacter (k := k) n hn f σ : (AlgebraicClosure F)ˣ) : AlgebraicClosure F) =
      σ (r : AlgebraicClosure F) / r :=
  ratio_eq_of_pow_eq (k := k) hn σ _ r ((kummerRoot_pow n hn f).trans hr.symm)

def kummerPairing (n : ℕ) (hn : 0 < n) :
    Fˣ →* ((AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) →*
      rootsOfUnity n (AlgebraicClosure F)) where
  toFun := kummerCharacter (k := k) n hn
  map_one' := by
    ext σ
    change ((kummerCharacter (k := k) n hn 1 σ : (AlgebraicClosure F)ˣ) : AlgebraicClosure F) = 1
    rw [kummerCharacter_apply_of_root n hn 1 σ 1 (by simp)]
    simp
  map_mul' f g := by
    ext σ
    change ((kummerCharacter (k := k) n hn (f * g) σ : (AlgebraicClosure F)ˣ) : AlgebraicClosure F) =
      ((kummerCharacter (k := k) n hn f σ : (AlgebraicClosure F)ˣ) : AlgebraicClosure F) *
      ((kummerCharacter (k := k) n hn g σ : (AlgebraicClosure F)ˣ) : AlgebraicClosure F)
    rw [kummerCharacter_apply_of_root n hn (f * g) σ (kummerRoot n hn f * kummerRoot n hn g) (by
      simp only [Units.val_mul, mul_pow, kummerRoot_pow, map_mul])]
    change σ ((kummerRoot n hn f : AlgebraicClosure F) * kummerRoot n hn g) /
      ((kummerRoot n hn f : AlgebraicClosure F) * kummerRoot n hn g) = _
    rw [map_mul, mul_div_mul_comm]
    rfl

theorem kummerCharacter_eq_one_iff (n : ℕ) (hn : 0 < n) (f : Fˣ)
    (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) :
    kummerCharacter (k := k) n hn f σ = 1 ↔
      σ (kummerRoot n hn f : AlgebraicClosure F) = kummerRoot n hn f := by
  constructor
  · intro h
    have hh := congrArg (fun z : rootsOfUnity n (AlgebraicClosure F) =>
      ((z : (AlgebraicClosure F)ˣ) : AlgebraicClosure F)) h
    exact (div_eq_one_iff_eq (kummerRoot n hn f).ne_zero).mp hh
  · intro h
    apply Subtype.ext
    apply Units.ext
    change σ (kummerRoot n hn f : AlgebraicClosure F) / kummerRoot n hn f = 1
    rw [h, div_self (kummerRoot n hn f).ne_zero]

theorem kummerCharacter_ker_isOpen (n : ℕ) (hn : 0 < n) (f : Fˣ) :
    IsOpen ((kummerCharacter (k := k) n hn f).ker :
      Set (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)) := by
  have he : ((kummerCharacter (k := k) n hn f).ker :
      Set (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)) =
      (MulAction.stabilizer (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)
        (kummerRoot n hn f : AlgebraicClosure F) : Set _) := by
    ext σ
    exact kummerCharacter_eq_one_iff (k := k) n hn f σ
  rw [he]
  exact stabilizer_isOpen_of_isIntegral _

theorem kummerCharacter_continuous (n : ℕ) (hn : 0 < n) (f : Fˣ) :
    Continuous (kummerCharacter (k := k) n hn f) := by
  apply continuous_of_continuousAt_one _ (continuousAt_def.mpr _)
  intro U hU
  have h1 : 1 ∈ U := by simpa only [map_one] using mem_of_mem_nhds hU
  have ho := kummerCharacter_ker_isOpen (k := k) n hn f
  exact Filter.mem_of_superset (ho.mem_nhds (Subgroup.one_mem _)) fun σ hσ => by
    change kummerCharacter (k := k) n hn f σ ∈ U
    rw [MonoidHom.mem_ker.mp hσ]
    exact h1

theorem kummerCharacter_proEllKernel (ell e : ℕ) (hell : 0 < ell) (f : Fˣ) :
    proEllKernel ell (Field.absoluteGaloisGroup F) ≤
      (kummerCharacter (k := k) (ell ^ e) (pow_pos hell e) f).ker := by
  let φ : Field.absoluteGaloisGroup F →* rootsOfUnity (ell ^ e) (AlgebraicClosure F) :=
    kummerCharacter (k := k) (ell ^ e) (pow_pos hell e) f
  let H : OpenNormalSubgroup (Field.absoluteGaloisGroup F) :=
    { φ.ker with isOpen' := kummerCharacter_ker_isOpen (k := k) _ _ f }
  have hp : IsPGroup ell (rootsOfUnity (ell ^ e) (AlgebraicClosure F)) := by
    intro z
    refine ⟨e, Subtype.ext ?_⟩
    exact z.property
  have hpQ : IsPGroup ell (Field.absoluteGaloisGroup F ⧸ H.toSubgroup) :=
    hp.of_injective (φ.range.subtype.comp (QuotientGroup.quotientKerEquivRange φ).toMonoidHom)
      (Subtype.val_injective.comp (QuotientGroup.quotientKerEquivRange φ).injective)
  exact iInf_le_of_le H (iInf_le_of_le hpQ le_rfl)

def kummerProEll (ell e : ℕ) (hell : 0 < ell) (f : Fˣ) :
    ProEll ell F →* rootsOfUnity (ell ^ e) (AlgebraicClosure F) :=
  QuotientGroup.lift _ (kummerCharacter (k := k) (ell ^ e) (pow_pos hell e) f)
    (kummerCharacter_proEllKernel ell e hell f)

theorem kummerProEll_continuous (ell e : ℕ) (hell : 0 < ell) (f : Fˣ) :
    Continuous (kummerProEll (k := k) ell e hell f) := by
  apply continuous_coinduced_dom.mpr
  exact kummerCharacter_continuous (k := k) (ell ^ e) (pow_pos hell e) f

theorem kummerProEll_closedCommutator (ell e : ℕ) (hell : 0 < ell) (f : Fˣ) :
    (commutator (ProEll ell F)).topologicalClosure ≤
      (kummerProEll (k := k) ell e hell f).ker := by
  apply Subgroup.topologicalClosure_minimal _
    (Abelianization.commutator_subset_ker (kummerProEll (k := k) ell e hell f))
  exact isClosed_singleton.preimage (kummerProEll_continuous ell e hell f)

def kummerPiA (ell e : ℕ) (hell : 0 < ell) (f : Fˣ) :
    PiA ell F →* rootsOfUnity (ell ^ e) (AlgebraicClosure F) :=
  QuotientGroup.lift _ (kummerProEll (k := k) ell e hell f)
    (kummerProEll_closedCommutator ell e hell f)

@[simp]
theorem kummerPiA_absolute (ell e : ℕ) (hell : 0 < ell) (f : Fˣ)
    (σ : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) :
    kummerPiA (k := k) ell e hell f (absoluteToPiA ell F σ) =
      kummerCharacter (k := k) (ell ^ e) (pow_pos hell e) f σ := rfl

end BogomolovPop

namespace BogomolovPop
open scoped Topology
open Filter
lemma kummerPiA_pairing_mul {k F : Type*} [Field k] [Field F] [Algebra k F] [IsAlgClosed k]
    (ell e : ℕ) (hell : 0 < ell) (f g : Fˣ) (σ : PiA ell F) :
    kummerPiA (k := k) ell e hell (f * g) σ =
      kummerPiA (k := k) ell e hell f σ * kummerPiA (k := k) ell e hell g σ := by
  obtain ⟨τ, rfl⟩ := absoluteToPiA_surjective (F := F) ell σ
  exact DFunLike.congr_fun (map_mul (kummerPairing (k := k) (ell ^ e) (pow_pos hell e)) f g) τ

def kummerPiAPairing {k F : Type*} [Field k] [Field F] [Algebra k F] [IsAlgClosed k]
    (ell e : ℕ) (hell : 0 < ell) : Fˣ →* (PiA ell F →* rootsOfUnity (ell ^ e) (AlgebraicClosure F)) where
  toFun := kummerPiA (k := k) ell e hell
  map_one' := by
    apply MonoidHom.ext
    intro σ
    obtain ⟨τ, rfl⟩ := absoluteToPiA_surjective (F := F) ell σ
    exact DFunLike.congr_fun (map_one (kummerPairing (k := k) (ell ^ e) (pow_pos hell e))) τ
  map_mul' f g := MonoidHom.ext (kummerPiA_pairing_mul ell e hell f g)

end BogomolovPop

end
end
end
end

end OAI


