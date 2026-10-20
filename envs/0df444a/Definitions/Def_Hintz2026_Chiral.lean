-- Prove2me | Definitions.Def_Hintz2026_Chiral
-- name    : Hintz2026_Chiral
-- status  : Definition
-- author  : @He Wang
-- created : 2026-10-19T15:51:25.30599+00:00
-- url     : https://prove2.me/theorems/82ae0cf1-63d3-4ad9-85e6-6f436008fdfb
-- title:
--   Hintz2026 — Chiralisation scaffolding: components, system predicates, inverse maps
-- statement:
--   Throughout, $(M,a,Q)$ is a subextremal Kerr–Newman background ($M>0$, $Q\neq 0$, $a^2+Q^2<M^2$), $\Delta=r^2-2Mr+a^2+Q^2$, $\bar\rho=r+ia\cos\theta$, $\bar\rho^*=r-ia\cos\theta$, $U=\{r>r_+,\ 0<\theta<\pi\}$, and $D^-=\sqrt{\Delta}\,\partial_r-i\,\partial_\theta,\quad D^+=\sqrt{\Delta}\,\partial_r+i\,\partial_\theta$ act through coordinate-slice derivatives; the mode parameters are $\omega,m\in\mathbb{R}$. Scaffolding for the local equivalence (1)⟺(4)⟺(7): the normalised chiral components $g_1^{(e)}=\psi_2+e\,i\psi_1/\sqrt{\Delta}$, $g_2^{(e)}=-2Q(k+e\,i s/\sqrt{\Delta})$ (positive spin) and $g_1^{(e)}=\psi_{-2}-e\,i\sqrt{\Delta}\psi_{-1}$, $g_2^{(e)}=2Q(n-e\,i\sqrt{\Delta}\ell)$ (negative spin), so that $y_e=\mathrm{pre}\cdot(g_1^{(e)},g_2^{(e)})$; the hypothesis bundles `PosDiff`/`NegDiff` (slice-differentiability at a point) and `PosSmooth`/`NegSmooth` ($C^\infty$ on $U$); the pointwise system predicates `Sys1PosAt`, `Sys1NegAt` (the four residuals vanish), `Sys4At` ($(D^\mp\mp A)y_\pm=(cI\mp B)y_\mp$) and `Sys7At` ($D^-z_+=Cz_-$, $D^+z_-=\operatorname{adj}(C)z_+$ for $z_+=\operatorname{adj}(X)y_+$, $z_-=X^*y_-$); the inverse chiral maps `invPos`, `invNeg`; entry lemmas for $A$, $B$, $cI\mp B$; the derivative rules for $1/\sqrt{\Delta}$ and $\sqrt{\Delta}$; and the $2\times2$ elimination lemmas used to invert the chiralisation.
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eqs (1), (3), (4), (7); local source Atlas/Perturbations/Hintz2026/{Eq1to4Identity,Eq1to4Pos,Eq1to4Neg,Equivalence1to4,ChiralSmooth,MainTheorem}.lean at commit aa3cc58 (no public Git remote)

import Definitions.Def_Hintz2026_System1

/-!
# Hintz 2026 — Chiralisation scaffolding: normalised components, system predicates, inverse maps

Source: Hintz, arXiv:2609.33661v1, eqs (1), (3), (4), (7).  Local source:
Atlas/Perturbations/Hintz2026/{Eq1to4Identity,Eq1to4Pos,Eq1to4Neg,Equivalence1to4,ChiralSmooth,MainTheorem}.lean
at commit aa3cc58.  Contains the normalised chiral components g±, the differentiability/C∞ hypothesis
bundles (`PosDiff`, `NegDiff`, `PosSmooth`, `NegSmooth`), the pointwise system predicates `Sys1PosAt`,
`Sys1NegAt`, `Sys4At`, `Sys7At`, the inverse chiral maps `invPos`, `invNeg`, and short entry/elimination
lemmas.  The residual identities, the (1)↔(4) equivalences and the main theorem are separate platform nodes.
-/

open Complex Function Matrix
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Hintz2026

variable (p : SubextremalKN)

-- ═══ from Eq1to4Identity.lean ═══

def g1 (e : ℝ) (F : PosFields) (x : Fin 2 -> ℝ) : ℂ :=
  F.psi2 x + ↑e * I * F.psi1 x / ↑(Real.sqrt (Del p (x 0)))

def g2 (e : ℝ) (F : PosFields) (x : Fin 2 -> ℝ) : ℂ :=
  -2 * ↑p.Q * (F.k x + ↑e * I * F.s x / ↑(Real.sqrt (Del p (x 0))))

theorem yPos_0 (e : ℝ) (F : PosFields) (x : Fin 2 -> ℝ) : yPos p e F x 0 = ↑(prePos p x) * g1 p e F x := by
  simp [yPos, g1]

theorem yPos_1 (e : ℝ) (F : PosFields) (x : Fin 2 -> ℝ) : yPos p e F x 1 = ↑(prePos p x) * g2 p e F x := by
  simp [yPos, g2]

theorem cpd0_inv_sqrtDel {x : Fin 2 -> ℝ} (hx : x ∈ U p) :
    cpd 0 (fun z => (↑(Real.sqrt (Del p (z 0))) : ℂ)⁻¹) x
      = -(↑((x 0 - p.M) / Real.sqrt (Del p (x 0))) : ℂ) / (↑(Real.sqrt (Del p (x 0))) : ℂ) ^ 2 := by
  unfold cpd
  have hD := Del_pos p hx.1
  have h1 : HasDerivAt (fun u => (↑(Real.sqrt (Del p u)) : ℂ)) (↑((x 0 - p.M) / Real.sqrt (Del p (x 0)))) (x 0) :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (x 0) (hasDerivAt_sqrtDel_r p hD)
  have hne : (↑(Real.sqrt (Del p (x 0))) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hD).ne'
  have h2 := h1.inv hne
  refine (h2.congr_of_eventuallyEq ?_).deriv
  filter_upwards with u; simp [Function.update, show (1 : Fin 2) ≠ 0 from by decide]

theorem cpd1_inv_sqrtDel (x : Fin 2 -> ℝ) :
    cpd 1 (fun z => (↑(Real.sqrt (Del p (z 0))) : ℂ)⁻¹) x = 0 := by
  unfold cpd
  have : (fun u => (↑(Real.sqrt (Del p ((update x 1 u) 0))) : ℂ)⁻¹) = fun _ => (↑(Real.sqrt (Del p (x 0))) : ℂ)⁻¹ := by
    funext u; simp [Function.update, show (0 : Fin 2) ≠ 1 from by decide]
  rw [this, deriv_const]

theorem diff_inv_sqrtDel_slice {x : Fin 2 -> ℝ} (hx : x ∈ U p) (k : Fin 2) :
    DifferentiableAt ℝ (fun u => (↑(Real.sqrt (Del p ((update x k u) 0))) : ℂ)⁻¹) (x k) := by
  fin_cases k
  · have hD := Del_pos p hx.1
    have h1 : HasDerivAt (fun u => (↑(Real.sqrt (Del p u)) : ℂ)) (↑((x 0 - p.M) / Real.sqrt (Del p (x 0)))) (x 0) :=
      Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (x 0) (hasDerivAt_sqrtDel_r p hD)
    have hne : (↑(Real.sqrt (Del p (x 0))) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.mpr hD).ne'
    refine ((h1.inv hne).congr_of_eventuallyEq ?_).differentiableAt
    filter_upwards with u; simp [Function.update]
  · show DifferentiableAt ℝ (fun u => (↑(Real.sqrt (Del p ((update x 1 u) 0))) : ℂ)⁻¹) (x 1)
    have : (fun u => (↑(Real.sqrt (Del p ((update x 1 u) 0))) : ℂ)⁻¹) = fun _ => (↑(Real.sqrt (Del p (x 0))) : ℂ)⁻¹ := by
      funext u; simp [Function.update]
    rw [this]; exact differentiableAt_const _

theorem Dm_const_mul (c : ℂ) (f : (Fin 2 -> ℝ) -> ℂ) (x : Fin 2 -> ℝ) :
    Dm p (fun z => c * f z) x = c * Dm p f x := by
  unfold Dm cpd; simp only [deriv_const_mul_field]; ring

theorem Dp_const_mul (c : ℂ) (f : (Fin 2 -> ℝ) -> ℂ) (x : Fin 2 -> ℝ) :
    Dp p (fun z => c * f z) x = c * Dp p f x := by
  unfold Dp cpd; simp only [deriv_const_mul_field]; ring

theorem diff_div_sqrtDel_slice {x : Fin 2 -> ℝ} (hx : x ∈ U p) (f : (Fin 2 -> ℝ) -> ℂ)
    (hf : ∀ k, DifferentiableAt ℝ (fun u => f (update x k u)) (x k)) (k : Fin 2) :
    DifferentiableAt ℝ (fun u => f (update x k u) / ↑(Real.sqrt (Del p ((update x k u) 0)))) (x k) := by
  simp only [div_eq_mul_inv]
  exact (hf k).mul (diff_inv_sqrtDel_slice p hx k)

theorem diff_const_mul_slice (c : ℂ) {x : Fin 2 -> ℝ} (f : (Fin 2 -> ℝ) -> ℂ)
    (hf : ∀ k, DifferentiableAt ℝ (fun u => f (update x k u)) (x k)) (k : Fin 2) :
    DifferentiableAt ℝ (fun u => c * f (update x k u)) (x k) := (hf k).const_mul c

structure PosDiff (F : PosFields) (x : Fin 2 -> ℝ) : Prop where
  psi2 : ∀ k, DifferentiableAt ℝ (fun u => F.psi2 (update x k u)) (x k)
  psi1 : ∀ k, DifferentiableAt ℝ (fun u => F.psi1 (update x k u)) (x k)
  k    : ∀ k, DifferentiableAt ℝ (fun u => F.k (update x k u)) (x k)
  s    : ∀ k, DifferentiableAt ℝ (fun u => F.s (update x k u)) (x k)

theorem g1_eq (e : ℝ) (F : PosFields) :
    g1 p e F = fun z => F.psi2 z + (↑e * I) * (F.psi1 z / ↑(Real.sqrt (Del p (z 0)))) := by
  funext z; unfold g1; ring

theorem g2_eq (e : ℝ) (F : PosFields) :
    g2 p e F = fun z => (-2 * ↑p.Q) * (F.k z + (↑e * I) * (F.s z / ↑(Real.sqrt (Del p (z 0))))) := by
  funext z; unfold g2; ring

theorem diff_g1_slice (e : ℝ) {F : PosFields} {x : Fin 2 -> ℝ} (hx : x ∈ U p) (hF : PosDiff F x) (k : Fin 2) :
    DifferentiableAt ℝ (fun u => g1 p e F (update x k u)) (x k) := by
  rw [g1_eq]
  exact (hF.psi2 k).add (((diff_div_sqrtDel_slice p hx F.psi1 hF.psi1 k)).const_mul _)

theorem diff_g2_slice (e : ℝ) {F : PosFields} {x : Fin 2 -> ℝ} (hx : x ∈ U p) (hF : PosDiff F x) (k : Fin 2) :
    DifferentiableAt ℝ (fun u => g2 p e F (update x k u)) (x k) := by
  rw [g2_eq]
  exact ((hF.k k).add (((diff_div_sqrtDel_slice p hx F.s hF.s k)).const_mul _)).const_mul _


-- ═══ from Eq1to4Pos.lean ═══

theorem A_00 (x : Fin 2 -> ℝ) : A p x 0 0 = 0 := by simp [A]

theorem A_01 (x : Fin 2 -> ℝ) : A p x 0 1 = -I * ↑p.Q * rhoBarStar p x / rhoBar p x ^ 2 := by simp [A]

theorem A_10 (x : Fin 2 -> ℝ) : A p x 1 0 = I * ↑p.Q * rhoBar p x / rhoBarStar p x ^ 2 := by simp [A]

theorem A_11 (x : Fin 2 -> ℝ) : A p x 1 1 = 0 := by simp [A]

theorem B_00 (sg om mm : ℝ) (x : Fin 2 -> ℝ) : Bmat p sg om mm x 0 0 = I * bcoeff p sg om mm x := by simp [Bmat]

theorem B_01 (sg om mm : ℝ) (x : Fin 2 -> ℝ) : Bmat p sg om mm x 0 1 = I * (3 * (↑p.M * rhoBar p x - ↑(p.Q ^ 2)) / (↑p.Q * rhoBar p x)) := by simp [Bmat]

theorem B_10 (sg om mm : ℝ) (x : Fin 2 -> ℝ) : Bmat p sg om mm x 1 0 = I * (3 * ↑p.Q * rhoBar p x / rhoBarStar p x ^ 2) := by simp [Bmat]

theorem B_11 (sg om mm : ℝ) (x : Fin 2 -> ℝ) : Bmat p sg om mm x 1 1 = I * -bcoeff p sg om mm x := by simp [Bmat]

theorem mulVec_entry0 (M : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 -> ℂ) : (M *ᵥ v) 0 = M 0 0 * v 0 + M 0 1 * v 1 := by
  simp [mulVec, dotProduct, Fin.sum_univ_two]

theorem mulVec_entry1 (M : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 2 -> ℂ) : (M *ᵥ v) 1 = M 1 0 * v 0 + M 1 1 * v 1 := by
  simp [mulVec, dotProduct, Fin.sum_univ_two]

theorem cIsubB_00 (sg om mm : ℝ) (x : Fin 2 -> ℝ) : (cscalar p sg om mm x • (1 : Matrix (Fin 2) (Fin 2) ℂ) - Bmat p sg om mm x) 0 0 = cscalar p sg om mm x - Bmat p sg om mm x 0 0 := by simp

theorem cIsubB_01 (sg om mm : ℝ) (x : Fin 2 -> ℝ) : (cscalar p sg om mm x • (1 : Matrix (Fin 2) (Fin 2) ℂ) - Bmat p sg om mm x) 0 1 = - Bmat p sg om mm x 0 1 := by simp

theorem cIsubB_10 (sg om mm : ℝ) (x : Fin 2 -> ℝ) : (cscalar p sg om mm x • (1 : Matrix (Fin 2) (Fin 2) ℂ) - Bmat p sg om mm x) 1 0 = - Bmat p sg om mm x 1 0 := by simp

theorem cIsubB_11 (sg om mm : ℝ) (x : Fin 2 -> ℝ) : (cscalar p sg om mm x • (1 : Matrix (Fin 2) (Fin 2) ℂ) - Bmat p sg om mm x) 1 1 = cscalar p sg om mm x - Bmat p sg om mm x 1 1 := by simp

theorem cIaddB_00 (sg om mm : ℝ) (x : Fin 2 -> ℝ) : (cscalar p sg om mm x • (1 : Matrix (Fin 2) (Fin 2) ℂ) + Bmat p sg om mm x) 0 0 = cscalar p sg om mm x + Bmat p sg om mm x 0 0 := by simp

theorem cIaddB_01 (sg om mm : ℝ) (x : Fin 2 -> ℝ) : (cscalar p sg om mm x • (1 : Matrix (Fin 2) (Fin 2) ℂ) + Bmat p sg om mm x) 0 1 = Bmat p sg om mm x 0 1 := by simp

theorem cIaddB_10 (sg om mm : ℝ) (x : Fin 2 -> ℝ) : (cscalar p sg om mm x • (1 : Matrix (Fin 2) (Fin 2) ℂ) + Bmat p sg om mm x) 1 0 = Bmat p sg om mm x 1 0 := by simp

theorem cIaddB_11 (sg om mm : ℝ) (x : Fin 2 -> ℝ) : (cscalar p sg om mm x • (1 : Matrix (Fin 2) (Fin 2) ℂ) + Bmat p sg om mm x) 1 1 = cscalar p sg om mm x + Bmat p sg om mm x 1 1 := by simp


-- ═══ from Eq1to4Neg.lean ═══

def g1N (e : ℝ) (G : NegFields) (x : Fin 2 -> ℝ) : ℂ :=
  G.psim2 x - ↑e * I * ↑(Real.sqrt (Del p (x 0))) * G.psim1 x

def g2N (e : ℝ) (G : NegFields) (x : Fin 2 -> ℝ) : ℂ :=
  2 * ↑p.Q * (G.n x - ↑e * I * ↑(Real.sqrt (Del p (x 0))) * G.l x)

theorem yNeg_0 (e : ℝ) (G : NegFields) (x : Fin 2 -> ℝ) : yNeg p e G x 0 = ↑(preNeg p x) * g1N p e G x := by simp [yNeg, g1N]

theorem yNeg_1 (e : ℝ) (G : NegFields) (x : Fin 2 -> ℝ) : yNeg p e G x 1 = ↑(preNeg p x) * g2N p e G x := by simp [yNeg, g2N]

theorem cpd0_sqrtDel {x : Fin 2 -> ℝ} (hx : x ∈ U p) :
    cpd 0 (fun z => (↑(Real.sqrt (Del p (z 0))) : ℂ)) x = ↑((x 0 - p.M) / Real.sqrt (Del p (x 0))) := by
  unfold cpd
  have h1 : HasDerivAt (fun u => (↑(Real.sqrt (Del p u)) : ℂ)) (↑((x 0 - p.M) / Real.sqrt (Del p (x 0)))) (x 0) :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (x 0) (hasDerivAt_sqrtDel_r p (Del_pos p hx.1))
  refine (h1.congr_of_eventuallyEq ?_).deriv
  filter_upwards with u; simp [Function.update]

theorem cpd1_sqrtDel (x : Fin 2 -> ℝ) :
    cpd 1 (fun z => (↑(Real.sqrt (Del p (z 0))) : ℂ)) x = 0 := by
  unfold cpd
  have : (fun u => (↑(Real.sqrt (Del p ((update x 1 u) 0))) : ℂ)) = fun _ => (↑(Real.sqrt (Del p (x 0))) : ℂ) := by
    funext u; simp [Function.update]
  rw [this, deriv_const]

theorem diff_sqrtDel_slice {x : Fin 2 -> ℝ} (hx : x ∈ U p) (k : Fin 2) :
    DifferentiableAt ℝ (fun u => (↑(Real.sqrt (Del p ((update x k u) 0))) : ℂ)) (x k) := by
  fin_cases k
  · have h1 : HasDerivAt (fun u => (↑(Real.sqrt (Del p u)) : ℂ)) (↑((x 0 - p.M) / Real.sqrt (Del p (x 0)))) (x 0) :=
      Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (x 0) (hasDerivAt_sqrtDel_r p (Del_pos p hx.1))
    refine (h1.congr_of_eventuallyEq ?_).differentiableAt
    filter_upwards with u; simp [Function.update]
  · show DifferentiableAt ℝ (fun u => (↑(Real.sqrt (Del p ((update x 1 u) 0))) : ℂ)) (x 1)
    have : (fun u => (↑(Real.sqrt (Del p ((update x 1 u) 0))) : ℂ)) = fun _ => (↑(Real.sqrt (Del p (x 0))) : ℂ) := by
      funext u; simp [Function.update]
    rw [this]; exact differentiableAt_const _

structure NegDiff (G : NegFields) (x : Fin 2 -> ℝ) : Prop where
  psim2 : ∀ k, DifferentiableAt ℝ (fun u => G.psim2 (update x k u)) (x k)
  psim1 : ∀ k, DifferentiableAt ℝ (fun u => G.psim1 (update x k u)) (x k)
  n     : ∀ k, DifferentiableAt ℝ (fun u => G.n (update x k u)) (x k)
  l     : ∀ k, DifferentiableAt ℝ (fun u => G.l (update x k u)) (x k)

theorem g1N_eq (e : ℝ) (G : NegFields) :
    g1N p e G = fun z => G.psim2 z + (-(↑e * I)) * (↑(Real.sqrt (Del p (z 0))) * G.psim1 z) := by
  funext z; unfold g1N; ring

theorem g2N_eq (e : ℝ) (G : NegFields) :
    g2N p e G = fun z => (2 * ↑p.Q) * (G.n z + (-(↑e * I)) * (↑(Real.sqrt (Del p (z 0))) * G.l z)) := by
  funext z; unfold g2N; ring

theorem diff_sqrtDel_mul_slice {x : Fin 2 -> ℝ} (hx : x ∈ U p) (f : (Fin 2 -> ℝ) -> ℂ)
    (hf : ∀ k, DifferentiableAt ℝ (fun u => f (update x k u)) (x k)) (k : Fin 2) :
    DifferentiableAt ℝ (fun u => ↑(Real.sqrt (Del p ((update x k u) 0))) * f (update x k u)) (x k) :=
  (diff_sqrtDel_slice p hx k).mul (hf k)

theorem diff_g1N_slice (e : ℝ) {G : NegFields} {x : Fin 2 -> ℝ} (hx : x ∈ U p) (hG : NegDiff G x) (k : Fin 2) :
    DifferentiableAt ℝ (fun u => g1N p e G (update x k u)) (x k) := by
  rw [g1N_eq]; exact (hG.psim2 k).add ((diff_sqrtDel_mul_slice p hx G.psim1 hG.psim1 k).const_mul _)

theorem diff_g2N_slice (e : ℝ) {G : NegFields} {x : Fin 2 -> ℝ} (hx : x ∈ U p) (hG : NegDiff G x) (k : Fin 2) :
    DifferentiableAt ℝ (fun u => g2N p e G (update x k u)) (x k) := by
  rw [g2N_eq]; exact ((hG.n k).add ((diff_sqrtDel_mul_slice p hx G.l hG.l k).const_mul _)).const_mul _

theorem cpd_neg (k : Fin 2) (f : (Fin 2 -> ℝ) -> ℂ) (x : Fin 2 -> ℝ) :
    cpd k (fun z => -f z) x = -cpd k f x := by
  unfold cpd; exact deriv.neg


-- ═══ from Equivalence1to4.lean ═══

def Sys4At (sg om mm : ℝ) (yplus yminus : (Fin 2 -> ℝ) -> Fin 2 -> ℂ) (x : Fin 2 -> ℝ) : Prop :=
  (fun j => Dm p (fun z => yplus z j) x) - A p x *ᵥ yplus x =
      (cscalar p sg om mm x • (1 : Matrix (Fin 2) (Fin 2) ℂ) - Bmat p sg om mm x) *ᵥ yminus x ∧
  (fun j => Dp p (fun z => yminus z j) x) + A p x *ᵥ yminus x =
      (cscalar p sg om mm x • (1 : Matrix (Fin 2) (Fin 2) ℂ) + Bmat p sg om mm x) *ᵥ yplus x

def Sys1PosAt (om mm : ℝ) (F : PosFields) (x : Fin 2 -> ℝ) : Prop :=
  res1a p om mm F x = 0 ∧ res1b p om mm F x = 0 ∧ res1c p om mm F x = 0 ∧ res1d p om mm F x = 0

def Sys1NegAt (om mm : ℝ) (G : NegFields) (x : Fin 2 -> ℝ) : Prop :=
  res1aN p om mm G x = 0 ∧ res1bN p om mm G x = 0 ∧ res1cN p om mm G x = 0 ∧ res1dN p om mm G x = 0

theorem vec2_eq_iff (u v : Fin 2 -> ℂ) : u = v ↔ u 0 = v 0 ∧ u 1 = v 1 := by
  constructor
  · intro h; exact ⟨congr_fun h 0, congr_fun h 1⟩
  · rintro ⟨h0, h1⟩; funext i; fin_cases i <;> assumption

theorem sub_eq_iff_sub_sub (a b c : ℂ) : a - b = c ↔ a - b - c = 0 := by constructor <;> intro h <;> linear_combination h

theorem add_eq_iff_add_sub (a b c : ℂ) : a + b = c ↔ a + b - c = 0 := by constructor <;> intro h <;> linear_combination h

theorem elim_pm {s : ℂ} (hs : s ≠ 0) {a b : ℂ} (h1 : -I * a + b / s = 0) (h2 : I * a + b / s = 0) : a = 0 ∧ b = 0 := by
  have hb : b / s = 0 := by linear_combination (1/2 : ℂ) * h1 + (1/2 : ℂ) * h2
  have hb' : b = 0 := by rcases div_eq_zero_iff.mp hb with h | h; exact h; exact absurd h hs
  have ha : I * a = 0 := by linear_combination (-(1/2) : ℂ) * h1 + (1/2 : ℂ) * h2
  exact ⟨by rcases mul_eq_zero.mp ha with h | h; exact absurd h I_ne_zero; exact h, hb'⟩

theorem elim_pm' {s : ℂ} (hs : s ≠ 0) {a b : ℂ} (h1 : -I * a + s * b = 0) (h2 : I * a + s * b = 0) : a = 0 ∧ b = 0 := by
  have hb : s * b = 0 := by linear_combination (1/2 : ℂ) * h1 + (1/2 : ℂ) * h2
  have hb' : b = 0 := by rcases mul_eq_zero.mp hb with h | h; exact absurd h hs; exact h
  have ha : I * a = 0 := by linear_combination (-(1/2) : ℂ) * h1 + (1/2 : ℂ) * h2
  exact ⟨by rcases mul_eq_zero.mp ha with h | h; exact absurd h I_ne_zero; exact h, hb'⟩

theorem elim_pm_neg {s : ℂ} (hs : s ≠ 0) {a b : ℂ} (h1 : -I * a - s * b = 0) (h2 : I * a - s * b = 0) : a = 0 ∧ b = 0 := by
  have hb : s * b = 0 := by linear_combination (-(1/2) : ℂ) * h1 - (1/2 : ℂ) * h2
  have hb' : b = 0 := by rcases mul_eq_zero.mp hb with h | h; exact absurd h hs; exact h
  have ha : I * a = 0 := by linear_combination (-(1/2) : ℂ) * h1 + (1/2 : ℂ) * h2
  exact ⟨by rcases mul_eq_zero.mp ha with h | h; exact absurd h I_ne_zero; exact h, hb'⟩


-- ═══ from ChiralSmooth.lean ═══

theorem contDiffOn_Del : ContDiff ℝ ∞ (fun x : Fin 2 -> ℝ => Del p (x 0)) := by
  unfold Del; fun_prop

theorem contDiffOn_rpow_Del (q : ℝ) : ContDiffOn ℝ ∞ (fun x : Fin 2 -> ℝ => Real.rpow (Del p (x 0)) q) (U p) := by
  intro x hx
  have h : ContDiffAt ℝ ∞ (fun x : Fin 2 -> ℝ => Del p (x 0) ^ q) x :=
    ContDiffAt.rpow_const_of_ne (contDiffOn_Del p).contDiffAt (Del_pos p hx.1).ne'
  exact h.contDiffWithinAt

theorem contDiffOn_sqrt_sin : ContDiffOn ℝ ∞ (fun x : Fin 2 -> ℝ => Real.sqrt (Real.sin (x 1))) (U p) := by
  intro x hx
  have hsin : ContDiff ℝ ∞ (fun x : Fin 2 -> ℝ => Real.sin (x 1)) := Real.contDiff_sin.comp (contDiff_pi.mp contDiff_id 1)
  exact (hsin.contDiffAt.sqrt (sin_pos_of_mem p hx).ne').contDiffWithinAt

theorem contDiffOn_prePos : ContDiffOn ℝ ∞ (fun x => (↑(prePos p x) : ℂ)) (U p) :=
  Complex.ofRealCLM.contDiff.comp_contDiffOn ((contDiffOn_rpow_Del p (5/4)).mul (contDiffOn_sqrt_sin p))

theorem contDiffOn_preNeg : ContDiffOn ℝ ∞ (fun x => (↑(preNeg p x) : ℂ)) (U p) :=
  Complex.ofRealCLM.contDiff.comp_contDiffOn ((contDiffOn_rpow_Del p (-3/4)).mul (contDiffOn_sqrt_sin p))

theorem contDiffOn_sqrtDel_c : ContDiffOn ℝ ∞ (fun x => (↑(Real.sqrt (Del p (x 0))) : ℂ)) (U p) := by
  refine Complex.ofRealCLM.contDiff.comp_contDiffOn ?_
  intro x hx
  exact ((contDiffOn_Del p).contDiffAt.sqrt (Del_pos p hx.1).ne').contDiffWithinAt

theorem contDiffOn_inv_sqrtDel_c : ContDiffOn ℝ ∞ (fun x => ((↑(Real.sqrt (Del p (x 0))) : ℂ))⁻¹) (U p) :=
  (contDiffOn_sqrtDel_c p).inv (fun x hx => by exact_mod_cast (Real.sqrt_pos.mpr (Del_pos p hx.1)).ne')

structure PosSmooth (F : PosFields) : Prop where
  psi2 : ContDiffOn ℝ ∞ F.psi2 (U p)
  psi1 : ContDiffOn ℝ ∞ F.psi1 (U p)
  k    : ContDiffOn ℝ ∞ F.k (U p)
  s    : ContDiffOn ℝ ∞ F.s (U p)

structure NegSmooth (G : NegFields) : Prop where
  psim2 : ContDiffOn ℝ ∞ G.psim2 (U p)
  psim1 : ContDiffOn ℝ ∞ G.psim1 (U p)
  n     : ContDiffOn ℝ ∞ G.n (U p)
  l     : ContDiffOn ℝ ∞ G.l (U p)

theorem posDiff_of_smooth {F : PosFields} (hF : PosSmooth p F) {x : Fin 2 -> ℝ} (hx : x ∈ U p) : PosDiff F x :=
  ⟨fun k => differentiableAt_slice p hF.psi2 hx k, fun k => differentiableAt_slice p hF.psi1 hx k,
   fun k => differentiableAt_slice p hF.k hx k, fun k => differentiableAt_slice p hF.s hx k⟩

theorem negDiff_of_smooth {G : NegFields} (hG : NegSmooth p G) {x : Fin 2 -> ℝ} (hx : x ∈ U p) : NegDiff G x :=
  ⟨fun k => differentiableAt_slice p hG.psim2 hx k, fun k => differentiableAt_slice p hG.psim1 hx k,
   fun k => differentiableAt_slice p hG.n hx k, fun k => differentiableAt_slice p hG.l hx k⟩


-- ═══ from MainTheorem.lean ═══

def Sys7At (sg om mm : ℝ) (yplus yminus : (Fin 2 -> ℝ) -> Fin 2 -> ℂ) (x : Fin 2 -> ℝ) : Prop :=
  (fun i => Dm p (fun z => (adjugate (X p z) *ᵥ yplus z) i) x) = Cmat p sg om mm x *ᵥ ((X p x)ᴴ *ᵥ yminus x) ∧
  (fun i => Dp p (fun z => ((X p z)ᴴ *ᵥ yminus z) i) x) = adjugate (Cmat p sg om mm x) *ᵥ (adjugate (X p x) *ᵥ yplus x)

def invPos (yplus yminus : (Fin 2 -> ℝ) -> Fin 2 -> ℂ) : PosFields where
  psi2 := fun z => (yplus z 0 + yminus z 0) / (2 * ↑(prePos p z))
  psi1 := fun z => ↑(Real.sqrt (Del p (z 0))) * (yplus z 0 - yminus z 0) / (2 * I * ↑(prePos p z))
  k    := fun z => -(yplus z 1 + yminus z 1) / (4 * ↑p.Q * ↑(prePos p z))
  s    := fun z => -(↑(Real.sqrt (Del p (z 0))) * (yplus z 1 - yminus z 1)) / (4 * I * ↑p.Q * ↑(prePos p z))

def invNeg (yplus yminus : (Fin 2 -> ℝ) -> Fin 2 -> ℂ) : NegFields where
  psim2 := fun z => (yplus z 0 + yminus z 0) / (2 * ↑(preNeg p z))
  psim1 := fun z => -(yplus z 0 - yminus z 0) / (2 * I * ↑(Real.sqrt (Del p (z 0))) * ↑(preNeg p z))
  n     := fun z => (yplus z 1 + yminus z 1) / (4 * ↑p.Q * ↑(preNeg p z))
  l     := fun z => -(yplus z 1 - yminus z 1) / (4 * I * ↑p.Q * ↑(Real.sqrt (Del p (z 0))) * ↑(preNeg p z))

end Hintz2026

end


