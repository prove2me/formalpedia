-- Prove2me | Definitions.Def_ModularCurve_JZeroHeightFormPositivity
-- name    : ModularCurve_JZeroHeightFormPositivity
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:28.712661+00:00
-- url     : https://prove2.me/theorems/ff85ce61-5979-5831-b0f0-431184c56887
-- title:
--   Positivity data for the J₀(N) height form
-- statement:
--   Fix $N$ and work with the function field $\overline{\mathbb{Q}}\cdot$-model `modularFunctionFieldBar N`, its places, its divisors and the distinguished place `cuspInftyBar N`. Three real- or integer-valued quantities attached to a finite family $s=(s_i)_{i<r}$ of elements of that field are defined. For a divisor $D$, `offBaseMass N D` is the sum of the multiplicities $D(v)$ over all places $v$ other than `cuspInftyBar N`; `baseMass N s D` is the weighted sum $\sum_{v\neq\infty} D(v)\,\mathrm{baseHt}_s(\infty,v)$, where `baseHt` is the chord-defect height $\mathrm{pairHt}_s(v,\infty)=\mathrm{pointHt}_s(v)+\mathrm{pointHt}_s(\infty)-h(\mathrm{chordVec}_s(v,\infty))$ of the imported framework (zero at $v=\infty$); and `heightPairing N s v w` is the defect $\mathrm{baseHt}_s(\infty,v)+\mathrm{baseHt}_s(\infty,w)-\mathrm{pairHt}_s(v,w)$. The lemma `baseHt_eq_pointHt` records that for $v\neq\infty$ the base height equals the point height as soon as the chord vector of $v$ and $\infty$ has absolute logarithmic height $0$ and $\mathrm{pointHt}_s(\infty)=0$.
--
--   The structure `HeightFormPositivityData N K g' s μ`, for a finite extension $K/\mathbb{Q}$ inside $\overline{\mathbb{Q}}$, a degree $g'$ and a real slope $\mu$, is a proposition with three fields, each guarded by the hypothesis that $s$ is an embedding basis (linearly independent with span the Riemann–Roch space of $(2g+1)\infty$), and with $c$ ranging over the classes in $J_0(N)$ fixed by the fixing subgroup of $K$ and $D$ over their representatives in the sense of `IsRepOf` (effective, of the shape $E+g'\cdot\infty$ with $E$ of degree zero and class $c$, and Galois-stable under the fixing subgroup): `naiveHeight_le_baseMass` asserts the existence of $\kappa\ge 0$ and $C$ with `divNaiveHeight N K g' D` $\le\kappa\,$`baseMass N s D`$+C$ for all such $D$; `pairInteraction`, under $0<\mu$ and $\mathrm{genus}<\mu^2$, asserts the existence of constants $C$, $\eta_E>0$, $C_E$ and an exceptional set $Ex$ of pairs of places such that off $Ex$ one has $-\mu(\mathrm{baseHt}(v)+\mathrm{baseHt}(w))-C\le$ `heightPairing N s v w` for distinct $v,w\neq\infty$, while any class having a representative whose support meets an exceptional pair has some representative $D_0$ with $\eta_E\,$`divNaiveHeight N K g' D₀`$-C_E\le$ `heightForm N s D₀`; `multiPoint`, under $0<\mu$, asserts the existence of $\eta>0$ and $C$ such that any class with a representative $D$ satisfying $\mathrm{genus}\le\mu(\mathrm{offBaseMass}(D)-1)$ has a representative $D_2$ with $\eta\,$`baseMass N s D₂`$-C\le$ `heightForm N s D₂`.
--
--   Two degenerate instances are provided: the structure holds for all $g'$ and $\mu$ when $s$ is not an embedding basis, and it holds for $g'=0$, $\mu=0$, using that `divNaiveHeight N K 0 D` vanishes identically (the symmetric-function vector has a single entry) while the other two fields are vacuous for $\mu=0$.
--
--   **Relation to Mathlib.** The places, divisors, Riemann–Roch spaces, genus and height form used here belong to the project's own function-field framework; only the underlying absolute logarithmic height of a tuple of algebraic numbers is built on Mathlib's `Height.logHeight` for number fields.
--
--   **Where it is used.** These quantities and the positivity structure are the interface through which lower bounds for the height form on Galois-invariant classes of $J_0(N)$ are stated and consumed elsewhere in the tree; the present module supplies only the degenerate instances, the substantive ones being theorems about the curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_ModularCurve_JZeroHeightFormPositivity.lean

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option Elab.async false

open ModularCurve AlgebraicCurve

namespace ModularCurve.JZero

noncomputable def offBaseMass (N : ℕ) [NeZero N]
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : ℤ :=
  (D.erase (cuspInftyBar N)).sum fun _ m => m

noncomputable def baseMass (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : ℝ :=
  (D.erase (cuspInftyBar N)).sum fun v m => (m : ℝ) * baseHt s (cuspInftyBar N) v

noncomputable def heightPairing (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N)
    (v w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) : ℝ :=
  baseHt s (cuspInftyBar N) v + baseHt s (cuspInftyBar N) w - pairHt s v w

theorem baseHt_eq_pointHt (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N)
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (hv : v ≠ cuspInftyBar N)
    (hchord : absLogHeight (chordVec s v (cuspInftyBar N)) = 0)
    (hbase : pointHt s (cuspInftyBar N) = 0) :
    baseHt s (cuspInftyBar N) v = pointHt s v := by
  simp [baseHt, pairHt, hv, hchord, hbase]

structure HeightFormPositivityData (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (g' : ℕ) {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (μ : ℝ) : Prop where

  naiveHeight_le_baseMass :
    IsEmbBasis N s →
    ∃ κ C : ℝ, 0 ≤ κ ∧
      ∀ (c : ↥(JZero N ^+ ↥K.fixingSubgroup))
        (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
        IsRepOf N K g' c D →
        divNaiveHeight N K g' D ≤ κ * baseMass N s D + C

  pairInteraction :
    IsEmbBasis N s →
    0 < μ →
    (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ) < μ ^ 2 →
    ∃ C ηE CE : ℝ, 0 < ηE ∧
      ∃ Ex : Set (Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) ×
                  Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
        (∀ v w, v ≠ w → v ≠ cuspInftyBar N → w ≠ cuspInftyBar N → (v, w) ∉ Ex →
          -μ * (baseHt s (cuspInftyBar N) v + baseHt s (cuspInftyBar N) w) - C
            ≤ heightPairing N s v w) ∧
        (∀ (c : ↥(JZero N ^+ ↥K.fixingSubgroup))
           (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
           IsRepOf N K g' c D →
           (∃ v w, v ≠ w ∧ v ≠ cuspInftyBar N ∧ w ≠ cuspInftyBar N ∧
             D v ≠ 0 ∧ D w ≠ 0 ∧ (v, w) ∈ Ex) →
           ∃ D₀, IsRepOf N K g' c D₀ ∧
             ηE * divNaiveHeight N K g' D₀ - CE ≤ heightForm N s D₀)

  multiPoint :
    IsEmbBasis N s →
    0 < μ →
    ∃ η C : ℝ, 0 < η ∧
      ∀ (c : ↥(JZero N ^+ ↥K.fixingSubgroup))
        (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
        IsRepOf N K g' c D →
        (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ)
          ≤ μ * ((offBaseMass N D : ℝ) - 1) →
        ∃ D₂, IsRepOf N K g' c D₂ ∧
          η * baseMass N s D₂ - C ≤ heightForm N s D₂

theorem divNaiveHeight_zero_left (N : ℕ) [NeZero N] (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ K] (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    divNaiveHeight N K 0 D = 0 := by
  haveI : Subsingleton (Fin (0 + 1)) := ⟨fun a b => Fin.ext (by omega)⟩
  unfold divNaiveHeight
  split_ifs with h
  · exact Height.logHeight_eq_zero_of_subsingleton _
  · rfl

theorem divNaiveHeight_zero_left_le (N : ℕ) [NeZero N] (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    [FiniteDimensional ℚ K] (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (x : ℝ) :
    divNaiveHeight N K 0 D ≤ 0 * x + 0 := by
  rw [divNaiveHeight_zero_left, zero_mul, add_zero]

theorem heightFormPositivityData_of_not_isEmbBasis (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (g' : ℕ) {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (μ : ℝ)
    (hs : ¬ IsEmbBasis N s) : HeightFormPositivityData N K g' s μ where
  naiveHeight_le_baseMass := fun h => absurd h hs
  pairInteraction := fun h => absurd h hs
  multiPoint := fun h => absurd h hs

theorem heightFormPositivityData_zero (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    {r : ℕ} (s : Fin r → modularFunctionFieldBar N) :
    HeightFormPositivityData N K 0 s 0 where
  naiveHeight_le_baseMass := fun _ =>
    ⟨0, 0, le_rfl, fun _ D _ => divNaiveHeight_zero_left_le N K D _⟩
  pairInteraction := fun _ hμ => absurd hμ (lt_irrefl 0)
  multiPoint := fun _ hμ => absurd hμ (lt_irrefl 0)

end ModularCurve.JZero


