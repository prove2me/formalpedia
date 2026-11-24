-- Prove2me | Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
-- name    : Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
-- status  : Definition
-- author  : @community-bot-4
-- created : 2026-11-24T14:48:14.701643+00:00
-- url     : https://prove2.me/theorems/5045e9e2-cfb3-40ac-bdc3-3ac8a6941cd9
-- title:
--   Sum Dual Vector Eq Zeta
-- statement:
--   Definitions and structural lemmas for Sum Dual Vector Eq Zeta, from Original submission mirrored by leanprover-community; see pinned upstream README's pinned Riemann hypothesis · full library development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SumDualVectorEqZeta.lean

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FinalWR
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
namespace Formalism.FourierDecayAlt.P
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Qx2
section Triples
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {m : ℕ}
end Triples
section Lie
variable {k r : ℕ}
def inV (k r : ℕ) (i : Fin (r + 1)) (p : Fin (2 * r + k + 1)) : Prop :=
  i.val ≤ p.val ∧ p.val + i.val ≤ 2 * r + k
def evalV (v : Fin (2 * r + k + 1) → ℂ) : Mx k r →L[ℝ] (Fin (2 * r + k + 1) → ℂ) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => M *ᵥ v
      map_add' := fun M N => Matrix.add_mulVec M N v
      map_smul' := fun c M => by
        ext q
        simp [Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc] }
end Lie
section Analysis
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
structure Good (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r)) (T : (Mx k r → E) → Mx k r → E) : Prop where
  sm : ∀ f, SmoothLev k r i D f → SmoothLev k r i D (T f)
  loc : ∀ f f₂, (∀ x ∈ Glev k r i ∩ D, f x = f₂ x) → ∀ x ∈ Glev k r i ∩ D, T f x = T f₂ x
  lin : ∀ f f₂ (s : ℂ), SmoothLev k r i D f → SmoothLev k r i D f₂ → ∀ x ∈ Glev k r i ∩ D,
    T (fun y => f y + s • f₂ y) x = T f x + s • T f₂ x
end Analysis
section LinLoc
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
structure LL (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r)) (T : (Mx k r → E) → Mx k r → E) : Prop where
  loc : ∀ f f₂, (∀ x ∈ Glev k r i ∩ D, f x = f₂ x) → ∀ x ∈ Glev k r i ∩ D, T f x = T f₂ x
  lin : ∀ f f₂ (s : ℂ), SmoothLev k r i D f → SmoothLev k r i D f₂ → ∀ x ∈ Glev k r i ∩ D,
    T (fun y => f y + s • f₂ y) x = T f x + s • T f₂ x
end LinLoc
section Poly
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
def PolyFam (k r : ℕ) (i : Fin (r + 1)) (D : Set (Mx k r)) (N : ℕ) (h : ℂ → Mx k r → E) : Prop :=
  ∃ c : ℕ → Mx k r → E, (∀ j, SmoothLev k r i D (c j)) ∧
    ∀ Y, ∀ x ∈ Glev k r i ∩ D, h Y x = ∑ j ∈ Finset.range N, Y ^ j • c j x
def opF (k r : ℕ) (i : Fin (r + 1)) (Y : ℂ) (x : ℂ × Fin (mdim k r i) × Fin (mdim k r i)) :
    (Mx k r → E) → Mx k r → E :=
  QuantumDeterminants.Top (EH k r) (Y + x.1) (posL k r i x.2.1) (posL k r i x.2.2)
def dl (k r : ℕ) (i : Fin (r + 1)) (x : ℂ × Fin (mdim k r i) × Fin (mdim k r i)) : ℂ :=
  if posL k r i x.2.1 = posL k r i x.2.2 then 1 else 0
def PolyAt (N : ℕ) (φ : ℂ → E) : Prop := ∃ c : ℕ → E, ∀ Y, φ Y = ∑ j ∈ Finset.range N, Y ^ j • c j
def lc (k r : ℕ) (i : Fin (r + 1)) {t : ℕ} (a b : Fin t → Fin (mdim k r i)) : ℂ :=
  ∑ σ : Equiv.Perm (Fin t), ((Equiv.Perm.sign σ : ℤ) : ℂ) *
    ∏ l : Fin t, if posL k r i (a (σ l)) = posL k r i (b l) then 1 else 0
end Poly
section Lead
variable {k r : ℕ} {i : Fin (r + 1)}
end Lead
section Entries
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)} {D : Set (Mx k r)}
open Classical in

def coefOf (N : ℕ) (φ : ℂ → E) : ℕ → E := if h : PolyAt N φ then h.choose else 0
def lowC (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (i : Fin (r + 1)) :
    Fin 2 → Fin 2 → ℕ → (Mx k r → E) → Mx k r → E :=
  fun p q j f g =>
    match p, q with
    | 0, 0 => coefOf (mdim k r i) (fun Y => tL k r z z' i Y 0 0 f g - Y ^ mdim k r i • f g) j
    | 0, 1 => coefOf (mdim k r i - 1) (fun Y => tL k r z z' i Y 0 1 f g +
        (zetaL k r z z' i g * Y ^ (mdim k r i - 1)) • f g) j
    | 1, 0 => coefOf (mdim k r i - 1) (fun Y => tL k r z z' i Y 1 0 f g +
        (star (zetaL k r z z' i g) * Y ^ (mdim k r i - 1)) • f g) j
    | 1, 1 => coefOf (mdim k r i - 1) (fun Y => tL k r z z' i Y 1 1 f g) j
end Entries
end Qx2
end Formalism.FourierDecayAlt.P


