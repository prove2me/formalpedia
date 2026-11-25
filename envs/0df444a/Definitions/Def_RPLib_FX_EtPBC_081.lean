-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_081
-- name    : RPLib_FX_EtPBC_081
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T21:49:49.557795+00:00
-- url     : https://prove2.me/theorems/a05841ac-279b-50fc-9d2f-c065d731e639
-- title:
--   Proper base change for the projective line, library file 081
-- statement:
--   File 081 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_CovL3`: S4-EtPBC-A, R4-T2 (A1c): the tower of nilpotent lifts of a two-chart etale cover
--   * `S4.Def_RP_EtPBC_A_CovG3`: S4-EtPBC-A, R4-T2 (A2b): sections of `O(d)` lift along the whole tower, for one `d₀`
--   * `S4.Def_RP_EtPBC_A_Z2Pi0`: S4-EtPBC-A, (Z): idempotents of the fibre of a finite cover of `P¹_A` spread out to an etale neighbourhood
--   * `S4.Def_RP_EtPBC_A_Z3Two`: S4-EtPBC-A, (Z): the `π₀` lemma with localization hypotheses on the charts
--   * `S4.Def_RP_EtPBC_A_Z3Y`: S4-EtPBC-A, (Z) geometric layer 7 (G-b on `Y`): two-chart data of a finite `Y ⟶ P¹_V`
--   * `S4.Def_RP_EtPBC_A_Z3Alg`: S4-EtPBC-A, (Z) geometric layer 8 (G-d): the algebraic `π₀` lemma applied to a finite `Y ⟶ P¹_V`
--   * `S4.Def_RP_EtPBC_A_Z4FibA`: S4-EtPBC-A, (Z) geometric layer 11 (G-f, part 1): the fibre `Y_x` over a `K`-point `x` of `V`
--   * `S4.Def_RP_EtPBC_A_CovCh`: S4-EtPBC-A, R4-T2 (G1a): the fibre charts of a finite etale cover and the lift data `LiftD`
--   * `S4.Def_RP_EtPBC_A_CovCv`: S4-EtPBC-A, R4-T2 (G1c, part 1): the locally directed chart cover of `Y_{V'}`
--   * `S4.Def_RP_EtPBC_A_CovGl2`: S4-EtPBC-A, R4-T2 (G1c, part 2b): gluing finite etale chart algebras over `Y_{V'}`
--   * `S4.Def_RP_EtPBC_A_CovFib`: S4-EtPBC-A, R4-T2 (G1d): the lifted cover restricts to the given fibre cover
--   * `S4.Def_RP_EtPBC_A_Inj0d`: S4-EtPBC-A, G1d part 1: the open `good` (complement of the closed image of the support); `goodPt` is in `Inj0dg`
--   * `S4.Def_RP_EtPBC_A_DescG3`: S4-EtPBC-A, R4-T1c (part 2): the glued cover `U₀ ⟶ X` is finite, etale and surjective
--   * `S4.Def_RP_EtPBC_A_O2Sh3`: S4-EtPBC-A, O2 M6 (O2Sh3, part a): Shapiro's lemma for a separated etale `π = W.hom` of constant degree
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib
import Definitions.Def_RPLib_FX_EtPBC_071
import Definitions.Def_RPLib_FX_EtPBC_072
import Definitions.Def_RPLib_FX_EtPBC_073

/-!
# Proper base change for the projective line, library file 081

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_CovL3`: S4-EtPBC-A, R4-T2 (A1c): the tower of nilpotent lifts of a two-chart etale cover
* `S4.Def_RP_EtPBC_A_CovG3`: S4-EtPBC-A, R4-T2 (A2b): sections of `O(d)` lift along the whole tower, for one `d₀`
* `S4.Def_RP_EtPBC_A_Z2Pi0`: S4-EtPBC-A, (Z): idempotents of the fibre of a finite cover of `P¹_A` spread out to an etale neighbourhood
* `S4.Def_RP_EtPBC_A_Z3Two`: S4-EtPBC-A, (Z): the `π₀` lemma with localization hypotheses on the charts
* `S4.Def_RP_EtPBC_A_Z3Y`: S4-EtPBC-A, (Z) geometric layer 7 (G-b on `Y`): two-chart data of a finite `Y ⟶ P¹_V`
* `S4.Def_RP_EtPBC_A_Z3Alg`: S4-EtPBC-A, (Z) geometric layer 8 (G-d): the algebraic `π₀` lemma applied to a finite `Y ⟶ P¹_V`
* `S4.Def_RP_EtPBC_A_Z4FibA`: S4-EtPBC-A, (Z) geometric layer 11 (G-f, part 1): the fibre `Y_x` over a `K`-point `x` of `V`
* `S4.Def_RP_EtPBC_A_CovCh`: S4-EtPBC-A, R4-T2 (G1a): the fibre charts of a finite etale cover and the lift data `LiftD`
* `S4.Def_RP_EtPBC_A_CovCv`: S4-EtPBC-A, R4-T2 (G1c, part 1): the locally directed chart cover of `Y_{V'}`
* `S4.Def_RP_EtPBC_A_CovGl2`: S4-EtPBC-A, R4-T2 (G1c, part 2b): gluing finite etale chart algebras over `Y_{V'}`
* `S4.Def_RP_EtPBC_A_CovFib`: S4-EtPBC-A, R4-T2 (G1d): the lifted cover restricts to the given fibre cover
* `S4.Def_RP_EtPBC_A_Inj0d`: S4-EtPBC-A, G1d part 1: the open `good` (complement of the closed image of the support); `goodPt` is in `Inj0dg`
* `S4.Def_RP_EtPBC_A_DescG3`: S4-EtPBC-A, R4-T1c (part 2): the glued cover `U₀ ⟶ X` is finite, etale and surjective
* `S4.Def_RP_EtPBC_A_O2Sh3`: S4-EtPBC-A, O2 M6 (O2Sh3, part a): Shapiro's lemma for a separated etale `π = W.hom` of constant degree
-/

set_option autoImplicit false

-- ===== S4.Def_RP_EtPBC_A_CovL3 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A1c): the tower of nilpotent lifts of a two-chart etale cover

* **`TwoCov φb₀ φb₁ τ₀ τ₁`**: a two-chart finite etale cover (bundled rings, `RingHom.Etale`/`Finite` properties);
  **`TwoCovHom π₀ π₁ π C' C`**: a transition `C' → C` over reductions `πᵢ`, `π` (surjective, kernels, squares);
* **`exists_lift`**: `lift_step` in this language;
* levels `B ⧸ J^(k+1)`: `down` (square-zero kernel), `qmap` (with `isAwayMap_qmap`, `isUnit_qmap`, `qmap_down`);
* **`tower`**, **`towerHom`**: the lifts of a level-0 cover to all levels `k`, with transitions.
-/

set_option autoImplicit false

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Cov

end Cov

section Hom

end Hom

section Lift

end Lift

section Lvl

end Lvl

section Tower

variable {B₀ B₁ N : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] (φ₀ : B₀ →+* N) (φ₁ : B₁ →+* N)
  (J₀ : Ideal B₀) (J₁ : Ideal B₁) (JN : Ideal N) (h₀ : J₀.map φ₀ = JN) (h₁ : J₁.map φ₁ = JN) (t₀ : B₀) (t₁ : B₁)

variable (hφ₀ : IsAwayMap φ₀ t₀) (hφ₁ : IsAwayMap φ₁ t₁) (hu₀ : IsUnit (φ₀ t₀)) (hu₁ : IsUnit (φ₁ t₁))

include hφ₀ hφ₁ hu₀ hu₁

theorem exists_lvl_lift (k : ℕ) (C : LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k) :
    Nonempty (Σ C' : LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ (k + 1),
      TwoCovHom (down J₀ k) (down J₁ k) (down JN k) C' C) :=
  exists_lift _ _ _ _ (isAwayMap_qmap J₀ φ₀ JN h₀ t₀ hφ₀ hu₀ (k + 1))
    (isAwayMap_qmap J₁ φ₁ JN h₁ t₁ hφ₁ hu₁ (k + 1)) (isUnit_qmap J₀ φ₀ JN h₀ t₀ hu₀ (k + 1))
    (isUnit_qmap J₁ φ₁ JN h₁ t₁ hu₁ (k + 1)) _ _ _ (down_surj J₀ k) (down_surj J₁ k)
    (isNilpotent_ker_down J₀ k) (isNilpotent_ker_down J₁ k) _ _ (qmap_down J₀ φ₀ JN h₀ k)
    (qmap_down J₁ φ₁ JN h₁ k) C

variable (C₀ : LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ 0)

/-- **The tower** of lifts of the level-0 cover `C₀`. -/
def tower : (k : ℕ) → LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ k
  | 0 => C₀
  | k + 1 => (Classical.choice (exists_lvl_lift φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ k (tower k))).1

/-- **The transitions** of the tower. -/
def towerHom (k : ℕ) : TwoCovHom (down J₀ k) (down J₁ k) (down JN k)
    (tower φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀ (k + 1)) (tower φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀ k) :=
  (Classical.choice (exists_lvl_lift φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ k
    (tower φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀ k))).2

theorem tower_zero : tower φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀ 0 = C₀ := rfl

end Tower

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovG3 =====
section

/-!
# S4-EtPBC-A, R4-T2 (A2b): sections of `O(d)` lift along the whole tower, for one `d₀`

Charts `Bᵢ` with ring maps `ιBᵢ : R → Bᵢ` (agreeing in `N`) and `Jᵢ = p Bᵢ`, `JN = p N`:
* level maps **`lι₀`**, **`lι₁`** (`R → Eᵢ` at level `k`), **`lI`** (the ideal `p E`), `lι_compat`, `lhv`;
* along a transition: `lρι₀`, **`ker_ρ`** (`ker ρ = p^(k+1) E'`), `lq₀`, `lq₁`, `lqI` (`p^(k+1) · p E' = 0`), `lI_comap`;
* **`good_tower`**: generators with the same exponents at every level of `tower`;
* **`secMap_surj_tower`**: one `d₀` such that `secMap (towerHom k) d` is surjective for all `k` and `d ≥ d₀`.
-/

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

universe u

section Lv

end Lv

section Tower

variable {B₀ B₁ N R : Type u} [CommRing B₀] [CommRing B₁] [CommRing N] [CommRing R] (φ₀ : B₀ →+* N)
  (φ₁ : B₁ →+* N) (J₀ : Ideal B₀) (J₁ : Ideal B₁) (JN : Ideal N) (h₀ : J₀.map φ₀ = JN) (h₁ : J₁.map φ₁ = JN)
  (t₀ : B₀) (t₁ : B₁) (hφ₀ : IsAwayMap φ₀ t₀) (hφ₁ : IsAwayMap φ₁ t₁) (hu₀ : IsUnit (φ₀ t₀))
  (hu₁ : IsUnit (φ₁ t₁)) (C₀ : LCov φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ 0) (ιB₀ : R →+* B₀) (ιB₁ : R →+* B₁)
  (p : Ideal R)

include hφ₀ hφ₁ hu₀ hu₁

/-- **Generators with the same exponents at every level** of the tower. -/
theorem good_tower (hts : φ₀ t₀ * φ₁ t₁ = 1) (hB : (eval₂RingHom ιB₀ t₀).Finite) (hJ₀ : J₀ = p.map ιB₀) :
    ∃ (r : ℕ) (e : Fin r → ℕ), ∀ k, ∃ (m : Fin r → (tower φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀ k).E₀)
      (y : Fin r → (tower φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀ k).E₁),
      (tower φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀ k).Good
        (lι₀ ιB₀ (tower φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀ k))
        (lI ιB₀ p (tower φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀ k)) m y e := by
  obtain ⟨r, m, y, e, hG⟩ := good_zero_tower φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ C₀ ιB₀ p hts hB
  refine ⟨r, e, fun k => ?_⟩
  induction k with
  | zero => exact ⟨m, y, hG⟩
  | succ k ih =>
    obtain ⟨m, y, hk⟩ := ih
    let H := towerHom φ₀ φ₁ J₀ J₁ JN h₀ h₁ t₀ t₁ hφ₀ hφ₁ hu₀ hu₁ C₀ k
    exact H.good_lift (Ideal.Quotient.factor_mk _ _) _ _ (lρι₀ ιB₀ H) _ _ (lI_comap ιB₀ p H hJ₀) hk

end Tower

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_Z2Pi0 =====
section

/-!
# S4-EtPBC-A, (Z): idempotents of the fibre of a finite cover of `P¹_A` spread out to an etale neighbourhood

Algebraic form of the `π₀` lemma: `A` noetherian, `p` prime, chart algebras `B₀` (over `A[t]`), `B₁` (over `A[s]`),
both finite over `A[X]`, overlap algebra `N`, `φ₀ : B₀ →ₐ[A[X]] N`, `φ₁ : B₁ →ₐ[A] N`.

* `secAlg φ₀ φ₁`: the global sections `{(a, b) | φ₀ a = φ₁ b}` as an `A`-subalgebra of `B₀ × B₁`;
  `secAlg_finite`: it is finite over `A` (Z1, `twoChart_fg`).
* `fibreMap p φ₀ φ₁ : secAlg →ₐ[A] κ(p) ⊗ B₀ × κ(p) ⊗ B₁` and `fibreUnit p B₀ B₁`.
* `includeRight_eq_of_sub_mem`: `x ≡ y mod p B` gives `1 ⊗ x = 1 ⊗ y` in `κ(p) ⊗ B`.
* **`exists_etale_idem_twoChart`**: chart elements `ε₀`, `ε₁` idempotent mod `p` and agreeing mod `p` on the overlap
  come, after an etale `A → A'` with a prime `P` over `p` and `κ(p) ≅ κ(P)`, from an idempotent of `A' ⊗ secAlg`.
-/

set_option autoImplicit false

open Polynomial
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Z2

open RamanujanPetersson.EtPBC.Z1

universe u v w w'

variable {A : Type u} [CommRing A]

section Fib

end Fib

section TwoChart

variable {B₀ : Type v} {B₁ : Type w} {N : Type w'}
  [CommRing B₀] [Algebra A[X] B₀] [Algebra A B₀] [IsScalarTower A A[X] B₀]
  [CommRing B₁] [Algebra A[X] B₁] [Algebra A B₁] [IsScalarTower A A[X] B₁]
  [CommRing N] [Algebra A[X] N] [Algebra A N] [IsScalarTower A A[X] N]

/-- **`π₀` lemma, algebraic form.** Chart elements idempotent mod `p` and agreeing mod `p` on the overlap come, after
an etale `A → A'` with a prime `P` over `p` and `κ(p) ≅ κ(P)`, from an idempotent `e'` of `A' ⊗ secAlg`. -/
theorem exists_etale_idem_twoChart [IsNoetherianRing A] [Module.Finite A[X] B₀] [Module.Finite A[X] B₁]
    (p : Ideal A) [p.IsPrime] (φ₀ : B₀ →ₐ[A[X]] N) (φ₁ : B₁ →ₐ[A] N)
    (h₁ : ∀ m, (X : A[X]) • φ₁ ((X : A[X]) • m) = φ₁ m)
    (hgen : ∀ m : B₁, ∃ (d : ℕ) (a : B₀), φ₀ a = (X ^ d : A[X]) • φ₁ m)
    (hloc : ∀ y : N, ∃ (k : ℕ) (b : B₁), y = (X ^ k : A[X]) • φ₁ b)
    (hk₀ : ∀ a, φ₀ a = 0 → a ∈ xTors (A := A) B₀) (hk₁ : ∀ b, φ₁ b = 0 → b ∈ xTors (A := A) B₁)
    (ε₀ : B₀) (ε₁ : B₁) (h₀ : ε₀ * ε₀ - ε₀ ∈ p.map (algebraMap A B₀))
    (h₁' : ε₁ * ε₁ - ε₁ ∈ p.map (algebraMap A B₁)) (h₀₁ : φ₀ ε₀ - φ₁ ε₁ ∈ p.map (algebraMap A N)) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra A R') (_ : Algebra.Etale A R') (P : Ideal R')
      (_ : P.IsPrime) (_ : P.LiesOver p)
      (hbij : Function.Bijective (Ideal.ResidueField.mapₐ p P (Algebra.ofId _ _) (P.over_def p)))
      (e' : R' ⊗[A] secAlg φ₀ φ₁), IsIdempotentElem e' ∧
        Algebra.TensorProduct.lift
          (((fibreUnit p B₀ B₁).comp (AlgEquiv.ofBijective _ hbij).symm.toAlgHom).comp
            (IsScalarTower.toAlgHom A R' P.ResidueField)) (fibreMap p φ₀ φ₁) (fun _ _ => Commute.all _ _) e' =
          ((Algebra.TensorProduct.includeRight : B₀ →ₐ[A] p.ResidueField ⊗[A] B₀) ε₀,
            (Algebra.TensorProduct.includeRight : B₁ →ₐ[A] p.ResidueField ⊗[A] B₁) ε₁) := by
  have := secAlg_finite φ₀ φ₁ h₁ hgen hk₀ hk₁
  obtain ⟨a, b, hab, ha, hb, ha₀, hb₀⟩ := idem_twoChart p φ₀ φ₁ h₁ hgen hloc 0 ε₀ ε₁ h₀ h₁' h₀₁
  rw [zero_add, pow_one] at ha hb
  let y : secAlg φ₀ φ₁ := ⟨(a, b), hab⟩
  have hρ : fibreMap p φ₀ φ₁ y = ((Algebra.TensorProduct.includeRight : B₀ →ₐ[A] p.ResidueField ⊗[A] B₀) ε₀,
      (Algebra.TensorProduct.includeRight : B₁ →ₐ[A] p.ResidueField ⊗[A] B₁) ε₁) :=
    Prod.ext ((fibreMap_fst p φ₀ φ₁ y).trans (includeRight_eq_of_sub_mem p ha₀))
      ((fibreMap_snd p φ₀ φ₁ y).trans (includeRight_eq_of_sub_mem p hb₀))
  have hidem : IsIdempotentElem (fibreMap p φ₀ φ₁ y) := by
    unfold IsIdempotentElem
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_mul, fibreMap_fst, ← map_mul]
      exact includeRight_eq_of_sub_mem p ha
    · rw [Prod.snd_mul, fibreMap_snd, ← map_mul]
      exact includeRight_eq_of_sub_mem p hb
  obtain ⟨R', i₁, i₂, i₃, P, i₄, i₅, hbij, e', he', hmap⟩ :=
    exists_etale_idem p (fibreUnit p B₀ B₁) (fibreMap p φ₀ φ₁) y hidem
  exact ⟨R', i₁, i₂, i₃, P, i₄, i₅, hbij, e', he', hmap.trans hρ⟩

end TwoChart

end RamanujanPetersson.EtPBC.Z2

end

end

-- ===== S4.Def_RP_EtPBC_A_Z3Two =====
section

/-!
# S4-EtPBC-A, (Z): the `π₀` lemma with localization hypotheses on the charts

The charts of a finite cover of `P¹_A` are `B₀` (over `A[t]`) and `B₁` (over `A[s]`), the overlap `N` is both
`B₀[1/t]` and `B₁[1/s]`, and `t s = 1` on `N`. Here `X` acts as `t` on `B₀` and `N`, as `s` on `B₁`.

* `away_surj`, `away_zero`: the two halves of `IsLocalization.Away r S` in the form used below.
* **`exists_etale_idem_of_loc`**: `exists_etale_idem_twoChart` with the conditions `h₁`, `hgen`, `hloc`, `hk₀`, `hk₁`
  replaced by `t s = 1` and the localization conditions (`hs₀`, `hz₀` for `N = B₀[1/t]`, `hs₁`, `hz₁` for
  `N = B₁[1/s]`).
-/

set_option autoImplicit false

open Polynomial
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Z2

open RamanujanPetersson.EtPBC.Z1

universe u v w w'

section Away

end Away

variable {A : Type u} [CommRing A]
variable {B₀ : Type v} {B₁ : Type w} {N : Type w'}
  [CommRing B₀] [Algebra A[X] B₀] [Algebra A B₀] [IsScalarTower A A[X] B₀]
  [CommRing B₁] [Algebra A[X] B₁] [Algebra A B₁] [IsScalarTower A A[X] B₁]
  [CommRing N] [Algebra A[X] N] [Algebra A N] [IsScalarTower A A[X] N]

/-- **`π₀` lemma with localization hypotheses** (`t s = 1`, `N = B₀[1/t] = B₁[1/s]`). -/
theorem exists_etale_idem_of_loc [IsNoetherianRing A] [Module.Finite A[X] B₀] [Module.Finite A[X] B₁]
    (p : Ideal A) [p.IsPrime] (φ₀ : B₀ →ₐ[A[X]] N) (φ₁ : B₁ →ₐ[A] N)
    (hts : algebraMap A[X] N X * φ₁ (algebraMap A[X] B₁ X) = 1)
    (hs₀ : ∀ y : N, ∃ (k : ℕ) (a : B₀), algebraMap A[X] N X ^ k * y = φ₀ a)
    (hs₁ : ∀ y : N, ∃ (k : ℕ) (b : B₁), φ₁ (algebraMap A[X] B₁ X) ^ k * y = φ₁ b)
    (hz₀ : ∀ a, φ₀ a = 0 → ∃ k : ℕ, algebraMap A[X] B₀ X ^ k * a = 0)
    (hz₁ : ∀ b, φ₁ b = 0 → ∃ k : ℕ, algebraMap A[X] B₁ X ^ k * b = 0)
    (ε₀ : B₀) (ε₁ : B₁) (h₀ : ε₀ * ε₀ - ε₀ ∈ p.map (algebraMap A B₀))
    (h₁' : ε₁ * ε₁ - ε₁ ∈ p.map (algebraMap A B₁)) (h₀₁ : φ₀ ε₀ - φ₁ ε₁ ∈ p.map (algebraMap A N)) :
    ∃ (R' : Type u) (_ : CommRing R') (_ : Algebra A R') (_ : Algebra.Etale A R') (P : Ideal R')
      (_ : P.IsPrime) (_ : P.LiesOver p)
      (hbij : Function.Bijective (Ideal.ResidueField.mapₐ p P (Algebra.ofId _ _) (P.over_def p)))
      (e' : R' ⊗[A] secAlg φ₀ φ₁), IsIdempotentElem e' ∧
        Algebra.TensorProduct.lift
          (((fibreUnit p B₀ B₁).comp (AlgEquiv.ofBijective _ hbij).symm.toAlgHom).comp
            (IsScalarTower.toAlgHom A R' P.ResidueField)) (fibreMap p φ₀ φ₁) (fun _ _ => Commute.all _ _) e' =
          ((Algebra.TensorProduct.includeRight : B₀ →ₐ[A] p.ResidueField ⊗[A] B₀) ε₀,
            (Algebra.TensorProduct.includeRight : B₁ →ₐ[A] p.ResidueField ⊗[A] B₁) ε₁) := by
  have h₁ : ∀ m, (X : A[X]) • φ₁ ((X : A[X]) • m) = φ₁ m := by
    intro m
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← mul_assoc, hts, one_mul]
  have hgen : ∀ m : B₁, ∃ (d : ℕ) (a : B₀), φ₀ a = (X ^ d : A[X]) • φ₁ m := by
    intro m
    obtain ⟨k, a, ha⟩ := hs₀ (φ₁ m)
    exact ⟨k, a, by rw [← ha, Algebra.smul_def, map_pow]⟩
  have hloc : ∀ y : N, ∃ (k : ℕ) (b : B₁), y = (X ^ k : A[X]) • φ₁ b := by
    intro y
    obtain ⟨k, b, hb⟩ := hs₁ y
    refine ⟨k, b, ?_⟩
    rw [Algebra.smul_def, map_pow, ← hb, ← mul_assoc, ← mul_pow, hts, one_pow, one_mul]
  have hk₀ : ∀ a, φ₀ a = 0 → a ∈ xTors (A := A) B₀ := by
    intro a ha
    obtain ⟨k, hk⟩ := hz₀ a ha
    exact ⟨k, by rw [Algebra.smul_def, map_pow, hk]⟩
  have hk₁ : ∀ b, φ₁ b = 0 → b ∈ xTors (A := A) B₁ := by
    intro b hb
    obtain ⟨k, hk⟩ := hz₁ b hb
    exact ⟨k, by rw [Algebra.smul_def, map_pow, hk]⟩
  exact exists_etale_idem_twoChart p φ₀ φ₁ h₁ hgen hloc hk₀ hk₁ ε₀ ε₁ h₀ h₁' h₀₁

end RamanujanPetersson.EtPBC.Z2

end

end

-- ===== S4.Def_RP_EtPBC_A_Z3Y =====
section

/-!
# S4-EtPBC-A, (Z) geometric layer 7 (G-b on `Y`): two-chart data of a finite `Y ⟶ P¹_V`

For `π : Y ⟶ P¹_V` (`V` affine):
* `isAffineOpen_Qc`, `isAffineOpen_Yc`: the charts `Qᵢ` of `P¹_V` and `Yᵢ = π⁻¹ Qᵢ` are affine;
* `σY i j : Γ(V)[X] → Γ(Y, Yᵢ)` (`X ↦ π^*(Xⱼ/Xᵢ)`), **`finite_σY`** (`π` finite);
* `pull_res` (restriction commutes with pullback), **`basicOpen_tY`**, **`basicOpen_sY`**: `D(t) = D(s) = Y₀ ⊓ Y₁`;
* **`trans_Y`**: `t|_{Y₀₁} · s|_{Y₀₁} = 1`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace MvPolynomial HomogeneousLocalization
open RamanujanPetersson.EtCompact

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace RamanujanPetersson.EtPBC.Z3

universe u

variable (K : Type u) [Field K] {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K))

variable {Y : Scheme.{u}} (π : Y ⟶ PV K gV)

theorem basicOpen_tY : Y.basicOpen (π.app (Qc K gV 0) (tc K gV 0 1)) = Yc K gV π 0 ⊓ Yc K gV π 1 := by
  show Y.basicOpen (π.app _ ((pr K gV).app (chU K 0) (coord K 0 1))) = _
  rw [← Scheme.preimage_basicOpen, ← Scheme.preimage_basicOpen, basicOpen_coord, ← chU_eq]
  rfl

theorem basicOpen_sY : Y.basicOpen (π.app (Qc K gV 1) (tc K gV 1 0)) = Yc K gV π 0 ⊓ Yc K gV π 1 := by
  show Y.basicOpen (π.app _ ((pr K gV).app (chU K 1) (coord K 1 0))) = _
  rw [← Scheme.preimage_basicOpen, ← Scheme.preimage_basicOpen, basicOpen_coord, ← chU_eq, inf_comm]
  rfl

end RamanujanPetersson.EtPBC.Z3

end

end

-- ===== S4.Def_RP_EtPBC_A_Z3Alg =====
section

/-!
# S4-EtPBC-A, (Z) geometric layer 8 (G-d): the algebraic `π₀` lemma applied to a finite `Y ⟶ P¹_V`

`A = Γ(V)`, `B₀ = Γ(Y, Y₀)`, `B₁ = Γ(Y, Y₁)`, `N = Γ(Y, Y₀ ⊓ Y₁)`:
* `A[X]`-structures `algX0` (via `t`), `algX1` (via `s`), `algXN` (via `t`); `A`-structures `algA0`, `algA1`, `algAN`
  (structure maps of `Y ⟶ V`); towers `tow0`, `tow1`, `towN`; `res_struct`.
* `φY0 : B₀ →ₐ[A[X]] N`, `φY1 : B₁ →ₐ[A] N` (restrictions); `hts_Y`, `hs0_Y`, `hs1_Y`, `hz0_Y`, `hz1_Y`.
* **`exists_etale_idem_Y`**: chart elements idempotent mod `p` and agreeing mod `p` on the overlap come from an
  idempotent of `R' ⊗_A secAlg φY0 φY1` after an etale `R'` with a prime over `p` with the same residue field.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace HomogeneousLocalization
open RamanujanPetersson.EtCompact
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace RamanujanPetersson.EtPBC.Z3

universe u

variable (K : Type u) [Field K] {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K)) {Y : Scheme.{u}}
  (π : Y ⟶ PV K gV)

attribute [local instance] algX0 algX1 algXN algA0 algA1 algAN

attribute [local instance] tow0 tow1 towN

variable [IsAffine V] [IsFinite π]

theorem hs0_Y (y : Γ(Y, Yc K gV π 0 ⊓ Yc K gV π 1)) : ∃ (k : ℕ) (a : Γ(Y, Yc K gV π 0)),
    algebraMap (Polynomial Γ(V, ⊤)) Γ(Y, Yc K gV π 0 ⊓ Yc K gV π 1) Polynomial.X ^ k * y = φY0 K gV π a := by
  rw [algXN_X]
  exact res_away_surj (isAffineOpen_Yc K gV π 0) _ (basicOpen_tY K gV π).symm inf_le_left y

theorem hs1_Y (y : Γ(Y, Yc K gV π 0 ⊓ Yc K gV π 1)) : ∃ (k : ℕ) (b : Γ(Y, Yc K gV π 1)),
    φY1 K gV π (algebraMap (Polynomial Γ(V, ⊤)) Γ(Y, Yc K gV π 1) Polynomial.X) ^ k * y = φY1 K gV π b := by
  rw [algX1_X]
  exact res_away_surj (isAffineOpen_Yc K gV π 1) _ (basicOpen_sY K gV π).symm inf_le_right y

theorem hz0_Y (a : Γ(Y, Yc K gV π 0)) (ha : φY0 K gV π a = 0) :
    ∃ k : ℕ, algebraMap (Polynomial Γ(V, ⊤)) Γ(Y, Yc K gV π 0) Polynomial.X ^ k * a = 0 := by
  rw [algX0_X]
  exact res_away_zero (isAffineOpen_Yc K gV π 0) _ (basicOpen_tY K gV π).symm inf_le_left a ha

theorem hz1_Y (b : Γ(Y, Yc K gV π 1)) (hb : φY1 K gV π b = 0) :
    ∃ k : ℕ, algebraMap (Polynomial Γ(V, ⊤)) Γ(Y, Yc K gV π 1) Polynomial.X ^ k * b = 0 := by
  rw [algX1_X]
  exact res_away_zero (isAffineOpen_Yc K gV π 1) _ (basicOpen_sY K gV π).symm inf_le_right b hb

end RamanujanPetersson.EtPBC.Z3

end

end

-- ===== S4.Def_RP_EtPBC_A_Z4FibA =====
section

/-!
# S4-EtPBC-A, (Z) geometric layer 11 (G-f, part 1): the fibre `Y_x` over a `K`-point `x` of `V`

For `x : Spec K ⟶ V` with `x ≫ gV = 𝟙` (so `Γ(V) → Γ(Spec K)` is surjective):
* `Yx = Y ×_V Spec K`, `fx`, `sx`; for an open `U ⊆ Y`: `TU = Y_x ×_Y U`, `jT` (open immersion onto `fx⁻¹ U`), `kT`,
  `isPullback_T`, `isPushout_T` (`U` affine).
* **`fx_app_surj`**: `Γ(Y, U) → Γ(Y_x, fx⁻¹ U)` is surjective, **`ker_fx_app`**: its kernel is `(ker x^*) Γ(Y, U)`
  (`U` affine).
* `strU`, `strU_ρ`, `appTop_surj`, `isAffineOpen_Y01`, `Yx_sup`, `eq_of_res_x` (separation on the two charts of `Y_x`),
  `fx_res`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open RamanujanPetersson.EtCompact

noncomputable section

namespace RamanujanPetersson.EtPBC.Z3

universe u

section Fib

variable (K : Type u) [Field K] {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K)) {Y : Scheme.{u}}
  (π : Y ⟶ PV K gV)

theorem isAffineOpen_Y01 [IsAffine V] [IsAffineHom π] : IsAffineOpen (Yc K gV π 0 ⊓ Yc K gV π 1) := by
  rw [← basicOpen_tY]
  exact (isAffineOpen_Yc K gV π 0).basicOpen _

end Fib

end RamanujanPetersson.EtPBC.Z3

end

end

-- ===== S4.Def_RP_EtPBC_A_CovCh =====
section

/-!
# S4-EtPBC-A, R4-T2 (G1a): the fibre charts of a finite etale cover and the lift data `LiftD`

For `V` affine, `π : Y ⟶ P¹_V` finite, a `K`-point `x` of `V` and a finite etale `q : T ⟶ Y_x`, the charts
`Γ(Y_x, fx⁻¹ Yᵢ)` and `Γ(T, q⁻¹ fx⁻¹ Yᵢ)` satisfy every hypothesis of `CoverLiftAt`. **`nonempty_liftD`**: under
`CoverLiftAt K Γ(V) χ` (`χ` the point `x`), the lift data `LiftD` (= `CoverLift` at these charts) exist.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

open RamanujanPetersson.EtPBC.Z3

attribute [local instance] algX0 algX1 algXN algA0 algA1 algAN tow0 tow1 towN

universe u

variable (K : Type u) [Field K] {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K)) {Y : Scheme.{u}}
  (π : Y ⟶ PV K gV) (x : Spec (CommRingCat.of K) ⟶ V)

attribute [local instance] algKY

section Cover

variable {T : Scheme.{u}} (q : T ⟶ Yx K gV π x)

attribute [local instance] algT

theorem basicOpen_T0 : q ⁻¹ᵁ (fx K gV π x ⁻¹ᵁ (Yc K gV π 0 ⊓ Yc K gV π 1)) = T.basicOpen
    (algebraMap _ Γ(T, q ⁻¹ᵁ (fx K gV π x ⁻¹ᵁ Yc K gV π 0)) (((fx K gV π x).app (Yc K gV π 0)).hom
      (algebraMap (Polynomial Γ(V, ⊤)) Γ(Y, Yc K gV π 0) Polynomial.X))) := by
  rw [algX0_X, ← basicOpen_tY, Scheme.preimage_basicOpen, Scheme.preimage_basicOpen]
  rfl

theorem basicOpen_T1 : q ⁻¹ᵁ (fx K gV π x ⁻¹ᵁ (Yc K gV π 0 ⊓ Yc K gV π 1)) = T.basicOpen
    (algebraMap _ Γ(T, q ⁻¹ᵁ (fx K gV π x ⁻¹ᵁ Yc K gV π 1)) (((fx K gV π x).app (Yc K gV π 1)).hom
      (algebraMap (Polynomial Γ(V, ⊤)) Γ(Y, Yc K gV π 1) Polynomial.X))) := by
  rw [algX1_X, ← basicOpen_sY, Scheme.preimage_basicOpen, Scheme.preimage_basicOpen]
  rfl

theorem away_T0 [IsAffine V] [IsFinite π] [IsAffineHom q] : IsAwayMap (ψT0 K gV π x q)
    (algebraMap _ Γ(T, q ⁻¹ᵁ (fx K gV π x ⁻¹ᵁ Yc K gV π 0)) (((fx K gV π x).app (Yc K gV π 0)).hom
      (algebraMap (Polynomial Γ(V, ⊤)) Γ(Y, Yc K gV π 0) Polynomial.X))) := by
  have hU := (isAffineOpen_Wx K gV π x _ (isAffineOpen_Yc K gV π 0)).preimage q
  exact And.intro (fun y => res_away_surj hU _ (basicOpen_T0 K gV π x q) _ y)
    (fun a ha => res_away_zero hU _ (basicOpen_T0 K gV π x q) _ a ha)

theorem away_T1 [IsAffine V] [IsFinite π] [IsAffineHom q] : IsAwayMap (ψT1 K gV π x q)
    (algebraMap _ Γ(T, q ⁻¹ᵁ (fx K gV π x ⁻¹ᵁ Yc K gV π 1)) (((fx K gV π x).app (Yc K gV π 1)).hom
      (algebraMap (Polynomial Γ(V, ⊤)) Γ(Y, Yc K gV π 1) Polynomial.X))) := by
  have hU := (isAffineOpen_Wx K gV π x _ (isAffineOpen_Yc K gV π 1)).preimage q
  exact And.intro (fun y => res_away_surj hU _ (basicOpen_T1 K gV π x q) _ y)
    (fun a ha => res_away_zero hU _ (basicOpen_T1 K gV π x q) _ a ha)

end Cover

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovCv =====
section

/-!
# S4-EtPBC-A, R4-T2 (G1c, part 1): the locally directed chart cover of `Y_{V'}`

`directed_of_range`: directedness of an open cover from its ranges. **`covV`**: the open cover of `Y_{V'} = Y ×_V Spec R'`
by the charts `Spec (R' ⊗ Γ(Y₀₁))`, `Spec (R' ⊗ Γ(Y₀))`, `Spec (R' ⊗ Γ(Y₁))`, indexed by `WalkingSpan`
(`zero ↦ Y₀₁`), with transition maps the `span` of the chart restrictions `a0`, `a1`; instance `LocallyDirected`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

open RamanujanPetersson.EtPBC.Z3

attribute [local instance] algX0 algX1 algXN algA0 algA1 algAN tow0 tow1 towN

universe u

variable (K : Type u) [Field K] {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K)) {Y : Scheme.{u}}
  (π : Y ⟶ PV K gV) [IsAffine V] [IsAffineHom π] (R' : Type u) [CommRing R'] [Algebra Γ(V, ⊤) R']

/-- The chart over `Y₀₁`. -/
abbrev ch01 : Spec (CommRingCat.of (R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 0 ⊓ Yc K gV π 1))) ⟶ YV K gV π R' :=
  chY K gV π R' (isAffineOpen_Y01 K gV π) (hA01 K gV π)

theorem a0_ch0 : a0 K gV π R' ≫ ch0 K gV π R' = ch01 K gV π R' :=
  chY_res K gV π R' (isAffineOpen_Yc K gV π 0) (isAffineOpen_Y01 K gV π) inf_le_left (struct_res K gV π 0) (hA01 K gV π)
    (φ0V K gV π) rfl

theorem a1_ch1 : a1 K gV π R' ≫ ch1 K gV π R' = ch01 K gV π R' :=
  chY_res K gV π R' (isAffineOpen_Yc K gV π 1) (isAffineOpen_Y01 K gV π) inf_le_right (struct_res K gV π 1) (hA01 K gV π)
    (φY1 K gV π) rfl

/-- The chart maps, indexed by `WalkingSpan`. -/
def fV : (j : WalkingSpan) → (span (a0 K gV π R') (a1 K gV π R')).obj j ⟶ YV K gV π R'
  | none => ch01 K gV π R'
  | some WalkingPair.left => ch0 K gV π R'
  | some WalkingPair.right => ch1 K gV π R'

theorem trans_fV {i j : WalkingSpan} (h : i ⟶ j) :
    (span (a0 K gV π R') (a1 K gV π R')).map h ≫ fV K gV π R' j = fV K gV π R' i := by
  rcases h with _ | (_ | _)
  · exact Category.id_comp _
  · exact a0_ch0 K gV π R'
  · exact a1_ch1 K gV π R'

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovGl2 =====
section

/-!
# S4-EtPBC-A, R4-T2 (G1c, part 2b): gluing finite etale chart algebras over `Y_{V'}`

Chart algebras `E₀`, `E₁`, `E₀₁` over `R' ⊗ Γ(Y₀)`, `R' ⊗ Γ(Y₁)`, `R' ⊗ Γ(Y₀₁)`, glued by localizations `ψ₀`, `ψ₁` (the
data of `CoverLift`), give a relative gluing datum **`glD`** over the chart cover `covV`; its glued scheme maps to
`Y_{V'}` by **`toBase`**, which is finite and etale when `E₀`, `E₁` are.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

open RamanujanPetersson.EtPBC.Z3

attribute [local instance] algX0 algX1 algXN algA0 algA1 algAN tow0 tow1 towN

universe u

variable (K : Type u) [Field K] {V : Scheme.{u}} (gV : V ⟶ Spec (CommRingCat.of K)) {Y : Scheme.{u}}
  (π : Y ⟶ PV K gV)

theorem away0 [IsAffine V] [IsFinite π] :
    IsAwayMap (φ0V K gV π).toRingHom (algebraMap (Polynomial Γ(V, ⊤)) Γ(Y, Yc K gV π 0) Polynomial.X) := by
  refine ⟨fun y => ?_, fun a ha => hz0_Y K gV π a ha⟩
  obtain ⟨k, a, h⟩ := hs0_Y K gV π y
  refine ⟨k, a, ?_⟩
  show φY0 K gV π (algebraMap (Polynomial Γ(V, ⊤)) Γ(Y, Yc K gV π 0) Polynomial.X) ^ k * y = φY0 K gV π a
  rw [(φY0 K gV π).commutes]
  exact h

theorem away1 [IsAffine V] [IsFinite π] :
    IsAwayMap (φY1 K gV π).toRingHom (algebraMap (Polynomial Γ(V, ⊤)) Γ(Y, Yc K gV π 1) Polynomial.X) :=
  ⟨hs1_Y K gV π, hz1_Y K gV π⟩

section FinEt

end FinEt

section Et

end Et

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_CovFib =====
section

/-!
# S4-EtPBC-A, R4-T2 (G1d): the lifted cover restricts to the given fibre cover

For lift data `L : LiftD K gV π x q hx` of a fibre cover `q : T ⟶ Y_x`: the glued cover `dL L` of `Y_{V'}`
(`V' = Spec L.R'`), the lift `xL L` of `x`, and **`ψL L : U_x ⟶ T`** on `U_x = (dL L).glued ×_{Y_{V'}} Y_x`, glued
from the chart lifts `gW` (`g0`, `g1`; `overlap` on `Y₀₁`), with **`ψL_q`**: `ψL L ≫ q = pullback.snd`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open scoped TensorProduct

noncomputable section

namespace RamanujanPetersson.EtPBC.Cov

open RamanujanPetersson.EtPBC.Z3

attribute [local instance] algX0 algX1 algXN algA0 algA1 algAN tow0 tow1 towN algKY algT CoverLift.cR CoverLift.aR CoverLift.c₀ CoverLift.c₁ CoverLift.c₀₁ CoverLift.a₀ CoverLift.a₁ CoverLift.a₀₁

universe u

variable {K : Type u} [Field K] {V : Scheme.{u}} {gV : V ⟶ Spec (CommRingCat.of K)} {Y : Scheme.{u}}
  {π : Y ⟶ PV K gV} {x : Spec (CommRingCat.of K) ⟶ V} [IsAffine V] [IsFinite π] {hx : x ≫ gV = 𝟙 _}
  {T : Scheme.{u}} {q : T ⟶ Yx K gV π x} [IsAffineHom q] (L : LiftD K gV π x q hx)

theorem hT01 : IsAffineOpen (q ⁻¹ᵁ (fx K gV π x ⁻¹ᵁ (Yc K gV π 0 ⊓ Yc K gV π 1))) :=
  (isAffineOpen_Wx K gV π x _ (isAffineOpen_Y01 K gV π)).preimage q

theorem awpL0 : letI := algKV K gV; IsAwayMap (ψT0 K gV π x q) (L.θ₀ (algebraMap (L.R' ⊗[Γ(V, ⊤)] Γ(Y, Yc K gV π 0)) L.E₀
    ((1 : L.R') ⊗ₜ algebraMap (Polynomial Γ(V, ⊤)) Γ(Y, Yc K gV π 0) Polynomial.X))) := by
  letI := algKV K gV
  rw [L.hθ₀, map_one, map_one, one_mul]
  exact away_T0 K gV π x q

theorem ov_m0 : Spec.map (CommRingCat.ofHom (ψT0 K gV π x q)) ≫ (hT0 (q := q)).fromSpec = (hT01 (q := q)).fromSpec :=
  IsAffineOpen.map_fromSpec (hT0 (q := q)) (hT01 (q := q))
    (homOfLE (Scheme.Hom.preimage_mono q (Scheme.Hom.preimage_mono _ inf_le_left))).op

theorem ov_m1 : Spec.map (CommRingCat.ofHom (ψT1 K gV π x q)) ≫ (hT1 (q := q)).fromSpec = (hT01 (q := q)).fromSpec :=
  IsAffineOpen.map_fromSpec (hT1 (q := q)) (hT01 (q := q))
    (homOfLE (Scheme.Hom.preimage_mono q (Scheme.Hom.preimage_mono _ inf_le_right))).op

end RamanujanPetersson.EtPBC.Cov

end

end

-- ===== S4.Def_RP_EtPBC_A_Inj0d =====
section

/-!
# S4-EtPBC-A, G1d part 1: the open `good` (complement of the closed image of the support); `goodPt` is in `Inj0dg`
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech

universe u

variable (Λ : Type u) [CommRing Λ] {P S : Scheme.{u}} (g : P ⟶ S) (s : GeomPt S)

/-- The closed image in `V` of the support of `sec0 α`. -/
abbrev bad (j : Nbhd s) (G : EtSh Λ P) (α : Ext.{u} ((nbhdSys Λ g s).obj j) G 0) : Set j.1.left :=
  (pullback.fst j.1.hom g).base '' supp G (sec0 Λ g s j G α)

end RamanujanPetersson.EtPBC

end

end

-- ===== S4.Def_RP_EtPBC_A_DescG3 =====
section

/-!
# S4-EtPBC-A, R4-T1c (part 2): the glued cover `U₀ ⟶ X` is finite, etale and surjective

* Generic (any coequifibered `α : 𝒪_X ⟶ F` on affine opens): `glD H` (the relative gluing data),
  `cover_toBase` (`Spec F(U) ⟶ U₀ ⟶ X` is `Spec α_U ≫ U.fromSpec`), `prop_toBase` (a Zariski-local property holds
  for `toBase` once it holds for every `Spec α_U`), `isFinite_toBase`, `etale_toBase`, `surjective_toBase`.
* For `V` etale and surjective over `X` with `V.hom` affine: `surj_comap`, the instance
  `Module.FaithfullyFlat Γ(X, U) (CU V U)`, and for the descended presheaf `FU`:
  **`U0`**, **`toU0`** `: U0 ⟶ X` with `IsFinite`, `Etale`, `Surjective`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite

noncomputable section

namespace RamanujanPetersson.EtPBC.DescG

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtCompact RamanujanPetersson.EtCompact.Cech
  RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.DescA TensorProduct

universe u

section Base

end Base

section Cover

variable {X : Scheme.{u}} (V : X.Etale) [IsAffineHom V.hom]

variable [Surjective V.hom] {Λ : Type u} [CommRing Λ] {M : ModuleCat.{u} Λ} [Fintype M] [DecidableEq M]
  {E Q : EtSh Λ X} (a : constSh Λ X M ⟶ E) (b : E ⟶ Q) (hab : a ≫ b = 0)
  (hS : (ShortComplex.mk a b hab).ShortExact) (e : E.obj.obj (op V))
  (he : ∀ (W : X.Etale) (w₁ w₂ : W ⟶ V), (b.hom.app (op W)).hom ((E.obj.map w₁.op).hom e) =
    (b.hom.app (op W)).hom ((E.obj.map w₂.op).hom e))

instance isFinite_toU0 : IsFinite (toU0 V a b hab hS e he) :=
  isFinite_toBase _ fun U => RingHom.finite_algebraMap.2 (datA V a b hab hS e he U).finite_B

instance etale_toU0 : Etale (toU0 V a b hab hS e he) :=
  etale_toBase _ fun U => RingHom.etale_algebraMap.2 (datA V a b hab hS e he U).etale_B

end Cover

end RamanujanPetersson.EtPBC.DescG

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Sh3 =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Sh3, part a): Shapiro's lemma for a separated etale `π = W.hom` of constant degree

* **`shapExt Λ W n hn A k : Ext_W(π^* A, Λ_W) ≃+ Ext_P(A, Λ[W])`** (adjunction `π^* ⊣ π_*`, `π_*` exact, and
  `Λ[W] ≅ π_* Λ_W`); `shapExt_apply`; **`shapExt_natural`** (naturality in `A`);
* `shapH`, `shapFree` (cohomology forms): file O2Sh3b (split for kernel time).
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtShap

open RamanujanPetersson.EtSheaves RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact
  RamanujanPetersson.EtPBC.EtMV

universe u

variable (Λ : Type u) [CommRing Λ] {P : Scheme.{u}}

section Shap

variable (W : P.Etale) [QuasiCompact W.hom] [IsSeparated W.hom] (n : ℕ)
  (hn : ∀ y : P, Nat.card ((geomPtAt y).point.fiber.obj W) = n)

/-- **Shapiro**: `Ext_W(π^* A, Λ_W) ≃+ Ext_P(A, Λ[W])`. -/
def shapExt (A : EtSh Λ P) (k : ℕ) :
    Ext.{u} ((pull W.hom Λ).obj A) (unitSh Λ W.left) k ≃+ Ext.{u} A (freeSh Λ W) k :=
  haveI := push_preservesFiniteColimits_of_deg Λ W n hn
  (extAdjEquiv (pullAdj W.hom Λ) A (unitSh Λ W.left) k).trans
    (extIsoRight A (shapIso Λ W n hn).symm k)

end Shap

end RamanujanPetersson.EtPBC.EtShap

end

end


