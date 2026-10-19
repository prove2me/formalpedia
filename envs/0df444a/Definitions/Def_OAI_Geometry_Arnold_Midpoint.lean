-- Prove2me | Definitions.Def_OAI_Geometry_Arnold_Midpoint
-- name    : OAI_Geometry_Arnold_Midpoint
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T08:57:26.015374+00:00
-- url     : https://prove2.me/theorems/ddbb12db-7287-491c-a0eb-6b5c9684b65c
-- title:
--   Implicit midpoint steps of a Lipschitz field as a smooth Hamiltonian isotopy
-- statement:
--   Let $E$ be a real Banach space and $X:E\to E$ Lipschitz with constant $C$. Let $\tau:\mathbb{R}\to\mathbb{R}$ satisfy $|\tau(t)|\,C<1$ for all $t$.
--
--   1. **Contraction.** For $|s|C<1$, the map $u\mapsto z+sX(u)$ is a contraction with constant $|s|C$.
--   2. **Resolvent (midpoint centre).** $c(t,z)$ is the unique solution $u$ of
--   $$
--   u=z+\tau(t)\,X(u),
--   $$
--   i.e. $(I-\tau(t)X)^{-1}z$. If $X$ and $\tau$ are smooth, so is $c$, by the implicit function theorem: the partial derivative in $u$ is $I-\tau(t)\,DX(u)$, which is invertible.
--   3. **Midpoint step.**
--   $$
--   \Phi(t,z)=2c(t,z)-z=c(t,z)+\tau(t)\,X\bigl(c(t,z)\bigr).
--   $$
--   This is the implicit midpoint rule $z'=z+2\tau X\bigl(\tfrac{z+z'}{2}\bigr)$ with step $2\tau(t)$.
--      - The step with $-\tau$ has the same centre and undoes $\Phi$.
--      - $\Phi$ is smooth.
--      - $\Phi(t,\cdot)=\mathrm{id}$ when $\tau(t)=0$.
--      - The centre commutes with every linear map commuting with $X$.
--      - The derivative of the centre satisfies $Dc\,(a,v)=v+a\,\tau'(t)\,X(c)+\tau(t)\,DX(c)\,Dc\,(a,v)$.
--   4. **Hamiltonian structure.** Let $\sigma$ be a skew continuous bilinear form, and $K$ smooth with $\sigma(X(w),\cdot)=dK(w)$ near a point $u$. Then $DX(u)$ is $\sigma$-skew. Define the time-dependent function
--   $$
--   H(t,w)=2\,\tau'(t)\,K\bigl(c^{-}(t,w)\bigr),
--   $$
--   where $c^-$ is the centre for $-\tau$; it is smooth. Then $\partial_t\Phi(t,z)=2\,\partial_tc(t,z)$, and whenever $X$ is $\sigma$-Hamiltonian for $K$ near $c(t,z)$, for all $v$
--   $$
--   \sigma\bigl(\partial_t\Phi(t,z),v\bigr)=d_wH\bigl(t,\Phi(t,z)\bigr)[v].
--   $$
--
--   So the implicit midpoint discretization of a Hamiltonian flow, with a time-dependent step size, is itself an exact Hamiltonian isotopy, with explicit smooth inverse and generating function.
--
--   **Formalization Note** The names are `resolvent`, `step` and `hamiltonian`. The hypothesis on $\tau$ is `∀ t, ‖τ t‖ * C < 1`, with $C$ a nonnegative real Lipschitz constant. Some lemmas omit completeness of $E$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/Arnold/Midpoint.lean

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/Midpoint.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ArnoldCounterexample mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ArnoldCounterexample
import Definitions.Def_OAI_Geometry_Arnold_Involution
import Definitions.Def_OAI_Geometry_Arnold_Projective
import Definitions.Def_OAI_Geometry_Arnold_Rotation
import Definitions.Def_OAI_Geometry_Arnold_Tangent
import Definitions.Def_OAI_Geometry_Arnold_Haar
import Definitions.Def_OAI_Geometry_Arnold_Differentiation
import Definitions.Def_OAI_Geometry_Arnold_Orbit
import Definitions.Def_OAI_Geometry_Arnold_Symplectic
import Definitions.Def_OAI_Geometry_Arnold_Coordinates
import Definitions.Def_OAI_Geometry_Arnold_Extension
import Definitions.Def_OAI_Geometry_Arnold_Deformation
import Definitions.Def_OAI_Geometry_Arnold_Exterior
import Definitions.Def_OAI_Geometry_Arnold_Homotopy
import Definitions.Def_OAI_Geometry_Arnold_Volume
import Definitions.Def_OAI_Geometry_Arnold_Obstruction
import Definitions.Def_OAI_Geometry_Arnold_ThreePoints
import Definitions.Def_OAI_Geometry_Arnold_Factors
import Definitions.Def_OAI_Geometry_Arnold_Field
import Definitions.Def_OAI_Geometry_Arnold_CompactField

namespace OAI

universe uE

noncomputable section
open scoped BigOperators ContDiff

open scoped ContDiff Topology NNReal
open Set Filter

namespace ArnoldCounterexample.Midpoint
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
lemma contraction (X : E → E) {C : ℝ≥0} (hX : LipschitzWith C X)
    (s : ℝ) (z : E) (hs : ‖s‖ * C < 1) :
    ContractingWith (‖s‖₊ * C) (fun u ↦ z + s • X u) := by
  refine ⟨?_, ?_⟩
  · exact_mod_cast hs
  · apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm, add_sub_add_left_eq_sub, ← smul_sub, norm_smul, ← dist_eq_norm]
    simpa only [NNReal.coe_mul, coe_nnnorm, mul_assoc] using
      mul_le_mul_of_nonneg_left (hX.dist_le_mul x y) (norm_nonneg s)

/-- The inverse of id-sX, for a smooth uniformly small parameter s. -/
def resolvent (X : E → E) {C : ℝ≥0} (hX : LipschitzWith C X)
    (τ : ℝ → ℝ) (hτ : ∀ t, ‖τ t‖ * C < 1) (p : ℝ × E) : E :=
  (contraction X hX (τ p.1) p.2 (hτ p.1)).fixedPoint (fun u ↦ p.2 + τ p.1 • X u)

lemma resolvent_eq (X : E → E) {C : ℝ≥0} (hX : LipschitzWith C X)
    (τ : ℝ → ℝ) (hτ : ∀ t, ‖τ t‖ * C < 1) (p : ℝ × E) :
    resolvent X hX τ hτ p = p.2 + τ p.1 • X (resolvent X hX τ hτ p) := by
  exact ((contraction X hX (τ p.1) p.2 (hτ p.1)).fixedPoint_isFixedPt).symm

lemma resolvent_unique (X : E → E) {C : ℝ≥0} (hX : LipschitzWith C X)
    (τ : ℝ → ℝ) (hτ : ∀ t, ‖τ t‖ * C < 1) (p : ℝ × E) (u : E)
    (hu : u = p.2 + τ p.1 • X u) : u = resolvent X hX τ hτ p := by
  exact (contraction X hX (τ p.1) p.2 (hτ p.1)).fixedPoint_unique hu.symm

omit [CompleteSpace E] in
lemma implicit_partial (X : E → E) (hX : ContDiff ℝ ∞ X)
    (τ : ℝ → ℝ) (hτ : ContDiff ℝ ∞ τ) (p : ℝ × E) (u : E) :
    fderiv ℝ (fun q : (ℝ × E) × E ↦ q.2 - q.1.2 - τ q.1.1 • X q.2) (p,u) ∘L
      ContinuousLinearMap.inr ℝ (ℝ × E) E =
        ContinuousLinearMap.id ℝ E - τ p.1 • fderiv ℝ X u := by
  have hg : ContDiff ℝ ∞ (fun q : (ℝ × E) × E ↦ q.2 - q.1.2 - τ q.1.1 • X q.2) := by fun_prop
  have hu : HasFDerivAt (fun v ↦ v - p.2 - τ p.1 • X v)
      (ContinuousLinearMap.id ℝ E - τ p.1 • fderiv ℝ X u) u :=
    ((hasFDerivAt_id u).sub_const p.2).sub ((hX.differentiable (by simp) u).hasFDerivAt.const_smul _)
  have hc := (hg.differentiable (by simp) (p,u)).hasFDerivAt.comp u
    ((hasFDerivAt_const p u).prodMk (hasFDerivAt_id (𝕜 := ℝ) u))
  convert hc.unique hu using 1; congr 1

lemma resolvent_smooth (X : E → E) {C : ℝ≥0} (hX : LipschitzWith C X)
    (hXs : ContDiff ℝ ∞ X) (τ : ℝ → ℝ) (hτ : ∀ t, ‖τ t‖ * C < 1)
    (hτs : ContDiff ℝ ∞ τ) : ContDiff ℝ ∞ (resolvent X hX τ hτ) := by
  rw [contDiff_iff_contDiffAt]
  intro p
  let u := resolvent X hX τ hτ p
  let g : (ℝ × E) × E → E := fun q ↦ q.2 - q.1.2 - τ q.1.1 • X q.2
  have hg : ContDiffAt ℝ ∞ g (p,u) := by dsimp [g]; fun_prop
  have hi : (fderiv ℝ g (p,u) ∘L ContinuousLinearMap.inr ℝ (ℝ × E) E).IsInvertible := by
    rw [show g = (fun q : (ℝ × E) × E ↦ q.2 - q.1.2 - τ q.1.1 • X q.2) from rfl,
      implicit_partial X hXs τ hτs]
    have hb : ‖τ p.1 • fderiv ℝ X u‖ < 1 := by
      rw [norm_smul]
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left
        (norm_fderiv_le_of_lipschitz ℝ hX) (norm_nonneg _)) (hτ p.1)
    obtain ⟨A,hA⟩ := isUnit_one_sub_of_norm_lt_one hb
    exact ⟨ContinuousLinearEquiv.ofUnit A, hA⟩
  apply (hg.contDiffAt_implicitFunction (by simp) hi).congr_of_eventuallyEq
  filter_upwards [hg.eventually_apply_implicitFunction (by simp) hi] with q hq
  have hbase : g (p,u) = 0 := by
    dsimp [g]
    have he := resolvent_eq X hX τ hτ p
    change u = _ at he
    calc
      u - p.2 - τ p.1 • X u = u - (p.2 + τ p.1 • X u) := by abel
      _ = 0 := sub_eq_zero.mpr he
  rw [hbase] at hq
  have hu : hg.implicitFunction (by simp) hi q = q.2 + τ q.1 • X (hg.implicitFunction (by simp) hi q) := by
    dsimp [g] at hq
    exact (sub_eq_iff_eq_add.mp (sub_eq_zero.mp hq)).trans (add_comm _ _)
  exact (resolvent_unique X hX τ hτ q _ hu).symm

lemma neg_small {C : ℝ≥0} {τ : ℝ → ℝ} (hτ : ∀ t, ‖τ t‖ * C < 1) :
    ∀ t, ‖-τ t‖ * C < 1 := by simpa only [norm_neg] using hτ

/-- The implicit midpoint step. The actual step size is 2τ. -/
def step (X : E → E) {C : ℝ≥0} (hX : LipschitzWith C X)
    (τ : ℝ → ℝ) (hτ : ∀ t, ‖τ t‖ * C < 1) (p : ℝ × E) : E :=
  (2 : ℝ) • resolvent X hX τ hτ p - p.2

lemma step_center (X : E → E) {C : ℝ≥0} (hX : LipschitzWith C X)
    (τ : ℝ → ℝ) (hτ : ∀ t, ‖τ t‖ * C < 1) (p : ℝ × E) :
    step X hX τ hτ p = resolvent X hX τ hτ p + τ p.1 • X (resolvent X hX τ hτ p) := by
  have he : resolvent X hX τ hτ p - p.2 = τ p.1 • X (resolvent X hX τ hτ p) := by
    exact sub_eq_iff_eq_add.mpr ((resolvent_eq X hX τ hτ p).trans (add_comm _ _))
  calc
    step X hX τ hτ p = resolvent X hX τ hτ p + (resolvent X hX τ hτ p - p.2) := by
      dsimp [step]; module
    _ = _ := by rw [he]

lemma resolvent_step (X : E → E) {C : ℝ≥0} (hX : LipschitzWith C X)
    (τ : ℝ → ℝ) (hτ : ∀ t, ‖τ t‖ * C < 1) (p : ℝ × E) :
    resolvent X hX (fun t ↦ -τ t) (neg_small hτ) (p.1, step X hX τ hτ p) =
      resolvent X hX τ hτ p := by
  symm
  apply resolvent_unique
  simp only [step_center, neg_smul]
  abel

lemma step_inverse (X : E → E) {C : ℝ≥0} (hX : LipschitzWith C X)
    (τ : ℝ → ℝ) (hτ : ∀ t, ‖τ t‖ * C < 1) (p : ℝ × E) :
    step X hX (fun t ↦ -τ t) (neg_small hτ) (p.1, step X hX τ hτ p) = p.2 := by
  rw [step, resolvent_step]
  dsimp [step]
  module

lemma step_smooth (X : E → E) {C : ℝ≥0} (hX : LipschitzWith C X)
    (hXs : ContDiff ℝ ∞ X) (τ : ℝ → ℝ) (hτ : ∀ t, ‖τ t‖ * C < 1)
    (hτs : ContDiff ℝ ∞ τ) : ContDiff ℝ ∞ (step X hX τ hτ) :=
  ((resolvent_smooth X hX hXs τ hτ hτs).const_smul (2 : ℝ)).sub contDiff_snd

lemma resolvent_zero (X : E → E) {C : ℝ≥0} (hX : LipschitzWith C X)
    (τ : ℝ → ℝ) (hτ : ∀ t, ‖τ t‖ * C < 1) (t : ℝ) (ht : τ t = 0) (z : E) :
    resolvent X hX τ hτ (t,z) = z := by
  simpa only [ht, zero_smul, add_zero] using resolvent_eq X hX τ hτ (t,z)

lemma step_zero (X : E → E) {C : ℝ≥0} (hX : LipschitzWith C X)
    (τ : ℝ → ℝ) (hτ : ∀ t, ‖τ t‖ * C < 1) (t : ℝ) (ht : τ t = 0) (z : E) :
    step X hX τ hτ (t,z) = z := by
  rw [step_center, resolvent_zero _ _ _ _ _ ht]
  simp [ht]

lemma resolvent_symmetry (X : E → E) {C : ℝ≥0} (hX : LipschitzWith C X)
    (τ : ℝ → ℝ) (hτ : ∀ t, ‖τ t‖ * C < 1) (S : E →ₗ[ℝ] E)
    (hS : ∀ z, X (S z) = S (X z)) (p : ℝ × E) :
    resolvent X hX τ hτ (p.1, S p.2) = S (resolvent X hX τ hτ p) := by
  symm
  apply resolvent_unique
  calc
    S (resolvent X hX τ hτ p) = S (p.2 + τ p.1 • X (resolvent X hX τ hτ p)) :=
      congrArg S (resolvent_eq X hX τ hτ p)
    _ = _ := by simp only [map_add, map_smul, hS]

lemma resolvent_fderiv_equation (X : E → E) {C : ℝ≥0} (hX : LipschitzWith C X)
    (hXs : ContDiff ℝ ∞ X) (τ : ℝ → ℝ) (hτ : ∀ t, ‖τ t‖ * C < 1)
    (hτs : ContDiff ℝ ∞ τ) (p : ℝ × E) (a : ℝ) (v : E) :
    fderiv ℝ (resolvent X hX τ hτ) p (a,v) = v +
      (a * deriv τ p.1) • X (resolvent X hX τ hτ p) +
        τ p.1 • fderiv ℝ X (resolvent X hX τ hτ p)
          (fderiv ℝ (resolvent X hX τ hτ) p (a,v)) := by
  let R := resolvent X hX τ hτ
  have hR := ((resolvent_smooth X hX hXs τ hτ hτs).differentiable (by simp) p).hasFDerivAt
  have hτR := ((hτs.differentiable (by simp) p.1).hasDerivAt).comp_hasFDerivAt p (hasFDerivAt_fst (𝕜 := ℝ) (p := p))
  have hXR := (hXs.differentiable (by simp) (R p)).hasFDerivAt.comp p hR
  have hd := hasFDerivAt_snd.add (hτR.smul hXR)
  have heq : (fun q : ℝ × E ↦ q.2 + τ q.1 • X (R q)) = R := by
    funext q
    exact (resolvent_eq X hX τ hτ q).symm
  change HasFDerivAt (fun q : ℝ × E ↦ q.2 + τ q.1 • X (R q)) _ p at hd
  rw [heq] at hd
  have he := congrArg (fun L : (ℝ × E) →L[ℝ] E ↦ L (a,v)) (hR.unique hd)
  change fderiv ℝ (resolvent X hX τ hτ) p (a,v) =
    v + (τ p.1 • fderiv ℝ X (resolvent X hX τ hτ p)
      (fderiv ℝ (resolvent X hX τ hτ) p (a,v)) +
      (deriv τ p.1 * a) • X (resolvent X hX τ hτ p)) at he
  simpa only [add_assoc, add_comm, add_left_comm, mul_comm] using he

omit [CompleteSpace E] in
lemma hamiltonian_linearization (σ : E →L[ℝ] E →L[ℝ] ℝ)
    (hσ : ∀ a b, σ a b = -σ b a) (X : E → E) (hX : ContDiff ℝ ∞ X)
    (K : E → ℝ) (hK : ContDiff ℝ ∞ K) (u : E)
    (hHK : ∀ᶠ w in 𝓝 u, σ (X w) = fderiv ℝ K w) (a b : E) :
    σ (fderiv ℝ X u a) b = -σ a (fderiv ℝ X u b) := by
  have hd := σ.hasFDerivAt.comp u ((hX.differentiable (by simp) u).hasFDerivAt)
  have hdK := hd.congr_of_eventuallyEq (show (fun w ↦ σ (X w)) =ᶠ[𝓝 u] fderiv ℝ K from hHK).symm
  have hs := (hK.contDiffAt (x := u)).isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top) a b
  rw [hdK.fderiv] at hs
  simpa only [ContinuousLinearMap.comp_apply, hσ _ a] using hs

end ArnoldCounterexample.Midpoint

namespace ArnoldCounterexample.Midpoint
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def hamiltonian (X : E → E) {C : ℝ≥0} (hX : LipschitzWith C X)
    (τ : ℝ → ℝ) (hτ : ∀ t, ‖τ t‖ * C < 1) (K : E → ℝ) (p : ℝ × E) : ℝ :=
  (2 * deriv τ p.1) * K (resolvent X hX (fun t ↦ -τ t) (neg_small hτ) p)

lemma hamiltonian_smooth (X : E → E) {C : ℝ≥0} (hX : LipschitzWith C X)
    (hXs : ContDiff ℝ ∞ X) (τ : ℝ → ℝ) (hτ : ∀ t, ‖τ t‖ * C < 1)
    (hτs : ContDiff ℝ ∞ τ) (K : E → ℝ) (hK : ContDiff ℝ ∞ K) :
    ContDiff ℝ ∞ (hamiltonian X hX τ hτ K) := by
  have hd : ContDiff ℝ ∞ (deriv τ) := hτs.deriv'
  exact (contDiff_const.mul (hd.comp contDiff_fst)).mul
    (hK.comp (resolvent_smooth X hX hXs _ (neg_small hτ) hτs.neg))

lemma step_time_derivative (X : E → E) {C : ℝ≥0} (hX : LipschitzWith C X)
    (hXs : ContDiff ℝ ∞ X) (τ : ℝ → ℝ) (hτ : ∀ t, ‖τ t‖ * C < 1)
    (hτs : ContDiff ℝ ∞ τ) (p : ℝ × E) :
    deriv (fun t ↦ step X hX τ hτ (t,p.2)) p.1 =
      (2 : ℝ) • fderiv ℝ (resolvent X hX τ hτ) p (1,0) := by
  have hR := ((resolvent_smooth X hX hXs τ hτ hτs).differentiable (by simp) p).hasFDerivAt
  have ht : HasDerivAt (fun t : ℝ ↦ (t,p.2)) (1,0) p.1 :=
    (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
  have hd := ((hR.comp_hasDerivAt p.1 ht).const_smul (2 : ℝ)).sub_const p.2
  exact hd.deriv

lemma step_hamiltonian_equation (σ : E →L[ℝ] E →L[ℝ] ℝ)
    (hσ : ∀ a b, σ a b = -σ b a) (X : E → E) {C : ℝ≥0} (hX : LipschitzWith C X)
    (hXs : ContDiff ℝ ∞ X) (τ : ℝ → ℝ) (hτ : ∀ t, ‖τ t‖ * C < 1)
    (hτs : ContDiff ℝ ∞ τ) (K : E → ℝ) (hK : ContDiff ℝ ∞ K) (p : ℝ × E)
    (hHK : ∀ᶠ w in 𝓝 (resolvent X hX τ hτ p), σ (X w) = fderiv ℝ K w) (v : E) :
    σ (deriv (fun t ↦ step X hX τ hτ (t,p.2)) p.1) v =
      fderiv ℝ (fun w ↦ hamiltonian X hX τ hτ K (p.1,w)) (step X hX τ hτ p) v := by
  let u := resolvent X hX τ hτ p
  let y := step X hX τ hτ p
  let A := fderiv ℝ (resolvent X hX τ hτ) p (1,0)
  let R := resolvent X hX (fun t ↦ -τ t) (neg_small hτ)
  let B := fderiv ℝ R (p.1,y) (0,v)
  have hRu : R (p.1,y) = u := resolvent_step X hX τ hτ p
  have hA : A = deriv τ p.1 • X u + τ p.1 • fderiv ℝ X u A := by
    simpa only [zero_add, one_mul] using resolvent_fderiv_equation X hX hXs τ hτ hτs p 1 0
  have hB : B = v - τ p.1 • fderiv ℝ X u B := by
    have h := resolvent_fderiv_equation X hX hXs (fun t ↦ -τ t) (neg_small hτ) hτs.neg (p.1,y) 0 v
    change B = v + (0 * deriv (fun t ↦ -τ t) p.1) • X (R (p.1,y)) +
      (-τ p.1) • fderiv ℝ X (R (p.1,y)) B at h
    simpa only [zero_mul, zero_smul, add_zero, hRu, neg_smul, sub_eq_add_neg] using h
  have hlin := hamiltonian_linearization σ hσ X hXs K hK u hHK A B
  have eeA : σ A B = deriv τ p.1 * σ (X u) B + τ p.1 * σ (fderiv ℝ X u A) B := by
    conv_lhs => rw [hA]
    simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
  have eeB : σ A B = σ A v - τ p.1 * σ A (fderiv ℝ X u B) := by
    conv_lhs => rw [hB]
    simp only [map_sub, map_smul, smul_eq_mul]
  have ee : σ A v = deriv τ p.1 * σ (X u) B := by rw [hlin] at eeA; nlinarith
  have hKX : fderiv ℝ K u = σ (X u) := (Filter.EventuallyEq.eq_of_nhds hHK).symm
  have hRd := ((resolvent_smooth X hX hXs _ (neg_small hτ) hτs.neg).differentiable (by simp) (p.1,y)).hasFDerivAt
  have hinc : HasFDerivAt (fun w : E ↦ (p.1,w)) (ContinuousLinearMap.inr ℝ ℝ E) y :=
    (hasFDerivAt_const p.1 y).prodMk (hasFDerivAt_id (𝕜 := ℝ) y)
  have hKd := (hK.differentiable (by simp) (R (p.1,y))).hasFDerivAt
  have hd := ((hKd.comp y (hRd.comp y hinc)).const_mul (2 * deriv τ p.1))
  change HasFDerivAt (fun w ↦ hamiltonian X hX τ hτ K (p.1,w)) _ y at hd
  rw [hd.fderiv, step_time_derivative X hX hXs τ hτ hτs p]
  change σ ((2 : ℝ) • A) v = _
  simp only [map_smul, smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply]
  rw [hRu, hKX]
  change 2 * σ A v = (2 * deriv τ p.1) * σ (X u) B
  rw [ee]
  ring

end ArnoldCounterexample.Midpoint

end

end OAI


