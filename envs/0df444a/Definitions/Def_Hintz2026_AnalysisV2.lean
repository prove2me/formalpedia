-- Prove2me | Definitions.Def_Hintz2026_AnalysisV2
-- name    : Hintz2026_AnalysisV2
-- status  : Definition
-- author  : @He Wang
-- created : 2026-10-19T13:42:19.212685+00:00
-- url     : https://prove2.me/theorems/887c1c83-7e4f-4aa7-bba0-28fe25079fb2
-- title:
--   Hintz2026 — Smoothness and C∞ field interface (infrastructure)
-- statement:
--   Infrastructure layer for the Hintz 2026 integrating-factor theory: real-analyticity of the entries of $X$, $X^{-1}$ and $(X^*)^{-1}$ on $U$; the coordinate-slice differentiability lemma for $C^\infty$ functions on the open set $U$; round-trip identities $X^{-1}(Xw) = w$ and $(X^*)^{-1}(X^*w) = w$; the $D^\pm$ Leibniz rules and matrix-vector product rules; and infrastructure used to prove the separately published pointwise $D^\pm$ residual identities. This bundle replaces `Hintz2026_Analysis`: the eighteen top-level results of the Sprint-01 audit (residual identities, solution correspondences, $C^\infty$ field interface, negative control) are published separately as theorems so that each carries its own proof node.
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eqs (4)-(6); local source Atlas/Perturbations/Hintz2026/{Smooth,Residual,SolutionCorr,FieldInterface}.lean at commit b328403 (no public Git remote)

import Definitions.Def_Hintz2026_Assembly

/-!
# Hintz 2026 — Smoothness, residual identities, solution correspondence, field interface
-/

open Complex Real Function Matrix Filter
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Hintz2026

variable (p : SubextremalKN)

-- ═══ From Smooth.lean ═══

/-!
# Hintz 2026 — Smoothness of X, A, X⁻¹, Y on U

ContDiffOn ℝ ⊤ (real analytic, `ω` in the pinned Mathlib) for all matrix entries
of X, A, X⁻¹, and Y = (Xᴴ)⁻¹ on U = {r > rPlus, 0 < θ < π}.
This implies real C∞ at order `∞` by `ContDiffOn.of_le le_top`.
-/





/-! ═══ Building blocks ═══ -/

private theorem smooth_r : ContDiff ℝ ⊤ (fun x : Fin 2 → ℝ => x 0) :=
  contDiff_pi.mp contDiff_id 0
private theorem smooth_th : ContDiff ℝ ⊤ (fun x : Fin 2 → ℝ => x 1) :=
  contDiff_pi.mp contDiff_id 1
private theorem smooth_Del : ContDiff ℝ ⊤ (fun x : Fin 2 → ℝ => Del p (x 0)) := by
  unfold Del; fun_prop
private theorem smooth_coe {f : (Fin 2 → ℝ) → ℝ} (hf : ContDiff ℝ ⊤ f) :
    ContDiff ℝ ⊤ (fun x => (↑(f x) : ℂ)) := Complex.ofRealCLM.contDiff.comp hf
private theorem smooth_sin : ContDiff ℝ ⊤ (fun x : Fin 2 → ℝ => Real.sin (x 1)) :=
  Real.contDiff_sin.comp smooth_th
private theorem smooth_complex_mk {f g : (Fin 2 → ℝ) → ℝ}
    (hf : ContDiff ℝ ⊤ f) (hg : ContDiff ℝ ⊤ g) :
    ContDiff ℝ ⊤ (fun x => (⟨f x, g x⟩ : ℂ)) := by
  have : (fun x => (⟨f x, g x⟩ : ℂ)) = fun x => ↑(f x) + ↑(g x) * I := by
    ext x; exact Complex.mk_eq_add_mul_I (f x) (g x)
  rw [this]; exact (smooth_coe hf).add ((smooth_coe hg).mul contDiff_const)

private theorem smooth_rhoBar : ContDiff ℝ ⊤ (rhoBar p) := by
  unfold rhoBar; exact smooth_complex_mk smooth_r ((Real.contDiff_cos.comp smooth_th).const_smul p.a)
private theorem smooth_rhoBarStar : ContDiff ℝ ⊤ (rhoBarStar p) := by
  unfold rhoBarStar; exact smooth_complex_mk smooth_r (((Real.contDiff_cos.comp smooth_th).const_smul p.a).neg)

private theorem contDiffOn_sqrtDel :
    ContDiffOn ℝ ⊤ (fun x : Fin 2 → ℝ => Real.sqrt (Del p (x 0))) (U p) := by
  intro x hx; exact ((smooth_Del p).contDiffAt.sqrt (ne_of_gt (Del_pos p hx.1))).contDiffWithinAt
private theorem contDiffOn_coe_sqrtDel :
    ContDiffOn ℝ ⊤ (fun x => (↑(Real.sqrt (Del p (x 0))) : ℂ)) (U p) :=
  Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_sqrtDel p)

private theorem cdoU_inv_rhoBar : ContDiffOn ℝ ⊤ (fun x => (rhoBar p x)⁻¹) (U p) :=
  (smooth_rhoBar p).contDiffOn.inv (fun x hx => rhoBar_ne_zero p hx)
private theorem cdoU_inv_rhoBarStar : ContDiffOn ℝ ⊤ (fun x => (rhoBarStar p x)⁻¹) (U p) :=
  (smooth_rhoBarStar p).contDiffOn.inv (fun x hx => rhoBarStar_ne_zero p hx)
private theorem cdoU_inv_rhoBar_sq : ContDiffOn ℝ ⊤ (fun x => ((rhoBar p x) ^ 2)⁻¹) (U p) :=
  ((smooth_rhoBar p).contDiffOn.pow 2).inv (fun x hx => pow_ne_zero 2 (rhoBar_ne_zero p hx))
private theorem cdoU_inv_rhoBarStar_sq : ContDiffOn ℝ ⊤ (fun x => ((rhoBarStar p x) ^ 2)⁻¹) (U p) :=
  ((smooth_rhoBarStar p).contDiffOn.pow 2).inv (fun x hx => pow_ne_zero 2 (rhoBarStar_ne_zero p hx))

/-! ═══ X entries ═══ -/

private theorem contDiffOn_X00 : ContDiffOn ℝ ⊤ (fun x => X p x 0 0) (U p) := by
  show ContDiffOn ℝ ⊤ (fun x =>
    ↑p.Q * (↑(Real.sqrt (Del p (x 0))) + ↑p.a * ↑(Real.sin (x 1))) / rhoBar p x) (U p)
  exact ContDiffOn.mul (ContDiffOn.mul contDiffOn_const
    ((contDiffOn_coe_sqrtDel p).add (ContDiffOn.mul contDiffOn_const (smooth_coe smooth_sin).contDiffOn)))
    (cdoU_inv_rhoBar p)

private theorem contDiffOn_X01 : ContDiffOn ℝ ⊤ (fun x => X p x 0 1) (U p) := by
  show ContDiffOn ℝ ⊤ (fun x => -I * (↑p.M - ↑(p.Q ^ 2) / rhoBar p x)) (U p)
  exact ContDiffOn.mul contDiffOn_const
    (contDiffOn_const.sub (ContDiffOn.mul contDiffOn_const (cdoU_inv_rhoBar p)))

private theorem contDiffOn_X10 : ContDiffOn ℝ ⊤ (fun x => X p x 1 0) (U p) := by
  show ContDiffOn ℝ ⊤ (fun x => I * (↑p.M - ↑(p.Q ^ 2) / rhoBarStar p x)) (U p)
  exact ContDiffOn.mul contDiffOn_const
    (contDiffOn_const.sub (ContDiffOn.mul contDiffOn_const (cdoU_inv_rhoBarStar p)))

private theorem contDiffOn_X11 : ContDiffOn ℝ ⊤ (fun x => X p x 1 1) (U p) := by
  show ContDiffOn ℝ ⊤ (fun x =>
    ↑p.Q * (↑(Real.sqrt (Del p (x 0))) - ↑p.a * ↑(Real.sin (x 1))) / rhoBarStar p x) (U p)
  exact ContDiffOn.mul (ContDiffOn.mul contDiffOn_const
    ((contDiffOn_coe_sqrtDel p).sub (ContDiffOn.mul contDiffOn_const (smooth_coe smooth_sin).contDiffOn)))
    (cdoU_inv_rhoBarStar p)

/-- Every entry of X is C∞ on U. -/
theorem contDiffOn_X_entry (i j : Fin 2) : ContDiffOn ℝ ⊤ (fun x => X p x i j) (U p) := by
  fin_cases i <;> fin_cases j
  · exact contDiffOn_X00 p
  · exact contDiffOn_X01 p
  · exact contDiffOn_X10 p
  · exact contDiffOn_X11 p

/-! ═══ A entries ═══ -/

private theorem contDiffOn_A01 : ContDiffOn ℝ ⊤ (fun x => A p x 0 1) (U p) := by
  show ContDiffOn ℝ ⊤ (fun x => -I * ↑p.Q * rhoBarStar p x / rhoBar p x ^ 2) (U p)
  exact ContDiffOn.mul (ContDiffOn.mul contDiffOn_const (smooth_rhoBarStar p).contDiffOn)
    (cdoU_inv_rhoBar_sq p)

private theorem contDiffOn_A10 : ContDiffOn ℝ ⊤ (fun x => A p x 1 0) (U p) := by
  show ContDiffOn ℝ ⊤ (fun x => I * ↑p.Q * rhoBar p x / rhoBarStar p x ^ 2) (U p)
  exact ContDiffOn.mul (ContDiffOn.mul contDiffOn_const (smooth_rhoBar p).contDiffOn)
    (cdoU_inv_rhoBarStar_sq p)

/-! ═══ X⁻¹ entries ═══ -/

private theorem contDiffOn_det_inv : ContDiffOn ℝ ⊤ (fun x => (X p x).det⁻¹) (U p) :=
  contDiffOn_const.congr (fun x hx => by rw [det_X p hx])

/-- Every entry of X⁻¹ is C∞ on U. Uses det(X) = const and adjugate formulas. -/
theorem contDiffOn_Xinv_entry (i j : Fin 2) :
    ContDiffOn ℝ ⊤ (fun x => (X p x)⁻¹ i j) (U p) := by
  have h00 : ContDiffOn ℝ ⊤ (fun x => (X p x)⁻¹ 0 0) (U p) :=
    ((contDiffOn_det_inv p).mul (contDiffOn_X11 p)).congr (fun x _ => Xinv_00 p x)
  have h01 : ContDiffOn ℝ ⊤ (fun x => (X p x)⁻¹ 0 1) (U p) :=
    ((contDiffOn_det_inv p).mul (contDiffOn_X01 p).neg).congr (fun x _ => Xinv_01 p x)
  have h10 : ContDiffOn ℝ ⊤ (fun x => (X p x)⁻¹ 1 0) (U p) :=
    ((contDiffOn_det_inv p).mul (contDiffOn_X10 p).neg).congr (fun x _ => Xinv_10 p x)
  have h11 : ContDiffOn ℝ ⊤ (fun x => (X p x)⁻¹ 1 1) (U p) :=
    ((contDiffOn_det_inv p).mul (contDiffOn_X00 p)).congr (fun x _ => Xinv_11 p x)
  fin_cases i <;> fin_cases j <;> assumption

/-! ═══ Y = (Xᴴ)⁻¹ entries ═══ -/

/-- Every entry of Y = (Xᴴ)⁻¹ is C∞ on U. Uses (Xᴴ)⁻¹ i j = star(X⁻¹ j i). -/
theorem contDiffOn_Y_entry (i j : Fin 2) :
    ContDiffOn ℝ ⊤ (fun x => ((X p x)ᴴ)⁻¹ i j) (U p) := by
  have key : ∀ x, ((X p x)ᴴ)⁻¹ i j = starRingEnd ℂ ((X p x)⁻¹ j i) := by
    intro x; rw [← conjTranspose_nonsing_inv, conjTranspose_apply]; rfl
  simp_rw [key]
  exact Complex.conjCLE.contDiff.comp_contDiffOn (contDiffOn_Xinv_entry p j i)

/-! ═══ Axiom audit ═══ -/



-- ═══ From Residual.lean ═══

/-!
# Hintz 2026 — Residual identities, solution correspondence, negative control

**C.** D₋(Xv) − A·(Xv) = X·(D₋v)  and  D₊(Yv) + A·(Yv) = Y·(D₊v)
**D.** Round-trip: X⁻¹(X·w)=w, X(X⁻¹·w)=w, Xᴴ(Y·w)=w, Y(Xᴴ·w)=w
**E.** Negative control: Dbad = √Δ·∂r fails the integrating-factor equation
-/





/-! ═══ cpd / Dm / Dp calculus ═══ -/

theorem cpd_mul (k : Fin 2) (f g : (Fin 2 → ℝ) → ℂ) (x : Fin 2 → ℝ)
    (hf : DifferentiableAt ℝ (fun u => f (update x k u)) (x k))
    (hg : DifferentiableAt ℝ (fun u => g (update x k u)) (x k)) :
    cpd k (fun z => f z * g z) x = cpd k f x * g x + f x * cpd k g x := by
  unfold cpd
  rw [show (fun u => f (update x k u) * g (update x k u)) =
      (fun u => f (update x k u)) * (fun u => g (update x k u)) from rfl,
      deriv_mul hf hg]; simp only [update_eq_self]

theorem cpd_add (k : Fin 2) (f g : (Fin 2 → ℝ) → ℂ) (x : Fin 2 → ℝ)
    (hf : DifferentiableAt ℝ (fun u => f (update x k u)) (x k))
    (hg : DifferentiableAt ℝ (fun u => g (update x k u)) (x k)) :
    cpd k (fun z => f z + g z) x = cpd k f x + cpd k g x := by
  unfold cpd
  rw [show (fun u => f (update x k u) + g (update x k u)) =
      (fun u => f (update x k u)) + (fun u => g (update x k u)) from rfl]
  exact deriv_add hf hg

theorem Dm_add (f g : (Fin 2 → ℝ) → ℂ) (x : Fin 2 → ℝ)
    (hf0 : DifferentiableAt ℝ (fun u => f (update x 0 u)) (x 0))
    (hg0 : DifferentiableAt ℝ (fun u => g (update x 0 u)) (x 0))
    (hf1 : DifferentiableAt ℝ (fun u => f (update x 1 u)) (x 1))
    (hg1 : DifferentiableAt ℝ (fun u => g (update x 1 u)) (x 1)) :
    Dm p (fun z => f z + g z) x = Dm p f x + Dm p g x := by
  unfold Dm; rw [cpd_add 0 f g x hf0 hg0, cpd_add 1 f g x hf1 hg1]; ring

theorem Dm_mul (f g : (Fin 2 → ℝ) → ℂ) (x : Fin 2 → ℝ)
    (hf0 : DifferentiableAt ℝ (fun u => f (update x 0 u)) (x 0))
    (hg0 : DifferentiableAt ℝ (fun u => g (update x 0 u)) (x 0))
    (hf1 : DifferentiableAt ℝ (fun u => f (update x 1 u)) (x 1))
    (hg1 : DifferentiableAt ℝ (fun u => g (update x 1 u)) (x 1)) :
    Dm p (fun z => f z * g z) x = Dm p f x * g x + f x * Dm p g x := by
  unfold Dm; rw [cpd_mul 0 f g x hf0 hg0, cpd_mul 1 f g x hf1 hg1]; ring

theorem Dp_add (f g : (Fin 2 → ℝ) → ℂ) (x : Fin 2 → ℝ)
    (hf0 : DifferentiableAt ℝ (fun u => f (update x 0 u)) (x 0))
    (hg0 : DifferentiableAt ℝ (fun u => g (update x 0 u)) (x 0))
    (hf1 : DifferentiableAt ℝ (fun u => f (update x 1 u)) (x 1))
    (hg1 : DifferentiableAt ℝ (fun u => g (update x 1 u)) (x 1)) :
    Dp p (fun z => f z + g z) x = Dp p f x + Dp p g x := by
  unfold Dp; rw [cpd_add 0 f g x hf0 hg0, cpd_add 1 f g x hf1 hg1]; ring

theorem Dp_mul (f g : (Fin 2 → ℝ) → ℂ) (x : Fin 2 → ℝ)
    (hf0 : DifferentiableAt ℝ (fun u => f (update x 0 u)) (x 0))
    (hg0 : DifferentiableAt ℝ (fun u => g (update x 0 u)) (x 0))
    (hf1 : DifferentiableAt ℝ (fun u => f (update x 1 u)) (x 1))
    (hg1 : DifferentiableAt ℝ (fun u => g (update x 1 u)) (x 1)) :
    Dp p (fun z => f z * g z) x = Dp p f x * g x + f x * Dp p g x := by
  unfold Dp; rw [cpd_mul 0 f g x hf0 hg0, cpd_mul 1 f g x hf1 hg1]; ring

/-! ═══ mulVec Leibniz ═══ -/

theorem Dm_mulVec_entry
    (M : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℂ)
    (w : (Fin 2 → ℝ) → Fin 2 → ℂ) (x : Fin 2 → ℝ) (i : Fin 2)
    (hM : ∀ j k, DifferentiableAt ℝ (fun u => M (update x k u) i j) (x k))
    (hw : ∀ j k, DifferentiableAt ℝ (fun u => w (update x k u) j) (x k)) :
    Dm p (fun z => (M z *ᵥ w z) i) x =
    (of fun a b => Dm p (fun z => M z a b) x).mulVec (w x) i +
    (M x).mulVec (fun j => Dm p (fun z => w z j) x) i := by
  simp only [mulVec, dotProduct, Fin.sum_univ_two, of_apply]
  rw [Dm_add p _ _ x ((hM 0 0).mul (hw 0 0)) ((hM 1 0).mul (hw 1 0))
                      ((hM 0 1).mul (hw 0 1)) ((hM 1 1).mul (hw 1 1)),
      Dm_mul p _ _ x (hM 0 0) (hw 0 0) (hM 0 1) (hw 0 1),
      Dm_mul p _ _ x (hM 1 0) (hw 1 0) (hM 1 1) (hw 1 1)]; ring

theorem Dp_mulVec_entry
    (M : (Fin 2 → ℝ) → Matrix (Fin 2) (Fin 2) ℂ)
    (w : (Fin 2 → ℝ) → Fin 2 → ℂ) (x : Fin 2 → ℝ) (i : Fin 2)
    (hM : ∀ j k, DifferentiableAt ℝ (fun u => M (update x k u) i j) (x k))
    (hw : ∀ j k, DifferentiableAt ℝ (fun u => w (update x k u) j) (x k)) :
    Dp p (fun z => (M z *ᵥ w z) i) x =
    (of fun a b => Dp p (fun z => M z a b) x).mulVec (w x) i +
    (M x).mulVec (fun j => Dp p (fun z => w z j) x) i := by
  simp only [mulVec, dotProduct, Fin.sum_univ_two, of_apply]
  rw [Dp_add p _ _ x ((hM 0 0).mul (hw 0 0)) ((hM 1 0).mul (hw 1 0))
                      ((hM 0 1).mul (hw 0 1)) ((hM 1 1).mul (hw 1 1)),
      Dp_mul p _ _ x (hM 0 0) (hw 0 0) (hM 0 1) (hw 0 1),
      Dp_mul p _ _ x (hM 1 0) (hw 1 0) (hM 1 1) (hw 1 1)]; ring

/-! ═══ C: Residual Identities ═══ -/

/-! ═══ D: Solution correspondence ═══ -/

theorem Xinv_X_mulVec {x : Fin 2 → ℝ} (hx : x ∈ U p) (w : Fin 2 → ℂ) :
    (X p x)⁻¹ *ᵥ (X p x *ᵥ w) = w := by
  rw [mulVec_mulVec, inv_mul_X p hx, one_mulVec]

theorem X_Xinv_mulVec {x : Fin 2 → ℝ} (hx : x ∈ U p) (w : Fin 2 → ℂ) :
    X p x *ᵥ ((X p x)⁻¹ *ᵥ w) = w := by
  rw [mulVec_mulVec, X_mul_inv p hx, one_mulVec]

theorem Xstar_Y_mulVec {x : Fin 2 → ℝ} (hx : x ∈ U p) (w : Fin 2 → ℂ) :
    (X p x)ᴴ *ᵥ (((X p x)ᴴ)⁻¹ *ᵥ w) = w := by
  rw [mulVec_mulVec, Xstar_mul_inv p hx, one_mulVec]

theorem Y_Xstar_mulVec {x : Fin 2 → ℝ} (hx : x ∈ U p) (w : Fin 2 → ℂ) :
    ((X p x)ᴴ)⁻¹ *ᵥ ((X p x)ᴴ *ᵥ w) = w := by
  rw [mulVec_mulVec, inv_mul_Xstar p hx, one_mulVec]

theorem Xinv_X_mulVec_eqOn (w : Fin 2 → ℂ) :
    Set.EqOn (fun z => (X p z)⁻¹ *ᵥ (X p z *ᵥ w)) (fun _ => w) (U p) :=
  fun _ hx => Xinv_X_mulVec p hx w

theorem X_Xinv_mulVec_eqOn (w : Fin 2 → ℂ) :
    Set.EqOn (fun z => X p z *ᵥ ((X p z)⁻¹ *ᵥ w)) (fun _ => w) (U p) :=
  fun _ hx => X_Xinv_mulVec p hx w

theorem Xstar_Y_mulVec_eqOn (w : Fin 2 → ℂ) :
    Set.EqOn (fun z => (X p z)ᴴ *ᵥ (((X p z)ᴴ)⁻¹ *ᵥ w)) (fun _ => w) (U p) :=
  fun _ hx => Xstar_Y_mulVec p hx w

theorem Y_Xstar_mulVec_eqOn (w : Fin 2 → ℂ) :
    Set.EqOn (fun z => ((X p z)ᴴ)⁻¹ *ᵥ ((X p z)ᴴ *ᵥ w)) (fun _ => w) (U p) :=
  fun _ hx => Y_Xstar_mulVec p hx w

/-! ═══ E: Negative control ═══ -/

/-- Wrong operator: Dbad = √Δ·∂r (missing the −I·∂θ term). -/
def Dbad (f : (Fin 2 → ℝ) → ℂ) (x : Fin 2 → ℝ) : ℂ :=
  ↑(Real.sqrt (Del p (x 0))) * cpd 0 f x

theorem Dbad_eq_Dm_add (f : (Fin 2 → ℝ) → ℂ) (x : Fin 2 → ℝ) :
    Dbad p f x = Dm p f x + I * cpd 1 f x := by
  unfold Dbad Dm; ring

/-! ═══ Axiom audit anchors ═══ -/



-- ═══ From SolutionCorr.lean ═══

/-!
# Hintz 2026 — Solution correspondence (iff)

D₋v = 0 ↔ D₋(Xv) − A(Xv) = 0, and D₊v = 0 ↔ D₊(Yv) + A(Yv) = 0,
with regularity-preserving forward/inverse maps.
-/





/-! ═══ mulVec invertibility ═══ -/

private theorem mulVec_eq_zero_iff {M : Matrix (Fin 2) (Fin 2) ℂ} (hM : IsUnit M.det)
    {w : Fin 2 → ℂ} : M *ᵥ w = 0 ↔ w = 0 := by
  constructor
  · intro h
    have : M⁻¹ *ᵥ (M *ᵥ w) = M⁻¹ *ᵥ 0 := congr_arg _ h
    rwa [mulVec_mulVec, nonsing_inv_mul _ hM, one_mulVec, mulVec_zero] at this
  · intro h; rw [h, mulVec_zero]

/-! ═══ D₋ solution correspondence ═══ -/

/-! ═══ D₊ solution correspondence ═══ -/

/-! ═══ Axiom audit ═══ -/



-- ═══ From FieldInterface.lean ═══

/-!
# Hintz 2026 — Field interface, reverse iff, negative-control witness

Unknown fields are real C∞ (`∞` in the `ContDiff` scope). The explicit
coefficients retain their stronger real-analytic order `⊤ = ω`; `of_le`
lowers only the coefficient regularity needed by the field interface.
-/





/-! ═══ Xᴴ entry smooth ═══ -/

/-! ═══ mulVec regularity ═══ -/

/-! ═══ DifferentiableAt discharge ═══ -/

private theorem differentiableAt_update (x : Fin 2 → ℝ) (k : Fin 2) :
    DifferentiableAt ℝ (update x k) (x k) := by
  apply differentiableAt_pi.mpr; intro i
  fin_cases k <;> fin_cases i <;> simp [update, Fin.val] <;>
    first | exact differentiableAt_id | exact differentiableAt_const _

theorem differentiableAt_slice {f : (Fin 2 → ℝ) → ℂ} (hf : ContDiffOn ℝ ∞ f (U p))
    {x : Fin 2 → ℝ} (hx : x ∈ U p) (k : Fin 2) :
    DifferentiableAt ℝ (fun u => f (update x k u)) (x k) := by
  have hdf : DifferentiableAt ℝ f x :=
    (hf.contDiffAt ((isOpen_U p).mem_nhds hx)).differentiableAt (by simp)
  conv at hdf => rw [show x = update x k (x k) from (update_eq_self k x).symm]
  exact hdf.comp (x k) (differentiableAt_update x k)

theorem hX_of_smooth {x : Fin 2 → ℝ} (hx : x ∈ U p) (i j k : Fin 2) :
    DifferentiableAt ℝ (fun u => X p (update x k u) i j) (x k) :=
  differentiableAt_slice p ((contDiffOn_X_entry p i j).of_le le_top) hx k

theorem hY_of_smooth {x : Fin 2 → ℝ} (hx : x ∈ U p) (i j k : Fin 2) :
    DifferentiableAt ℝ (fun u => (Matrix.conjTranspose (X p (update x k u)))⁻¹ i j) (x k) :=
  differentiableAt_slice p ((contDiffOn_Y_entry p i j).of_le le_top) hx k

theorem hv_of_smooth {v : (Fin 2 → ℝ) → Fin 2 → ℂ}
    (hv : ∀ j : Fin 2, ContDiffOn ℝ ∞ (fun x => v x j) (U p))
    {x : Fin 2 → ℝ} (hx : x ∈ U p) (j k : Fin 2) :
    DifferentiableAt ℝ (fun u => v (update x k u) j) (x k) :=
  differentiableAt_slice p (hv j) hx k

/-! ═══ Dm/Dp congr ═══ -/

theorem cpd_congr (k : Fin 2) {f g : (Fin 2 → ℝ) → ℂ} {x : Fin 2 → ℝ}
    (hU : x ∈ U p) (h : Set.EqOn f g (U p)) : cpd k f x = cpd k g x := by
  unfold cpd; apply Filter.EventuallyEq.deriv_eq
  have hcont : Continuous (fun u : ℝ => update x k u) := continuous_pi (fun i => by
    by_cases hi : i = k
    · subst hi; simp only [update_self]; exact continuous_id
    · simp only [update_of_ne hi]; exact continuous_const)
  exact eventually_of_mem
    (hcont.continuousAt.preimage_mem_nhds ((isOpen_U p).mem_nhds (by simp [update_eq_self]; exact hU)))
    (fun u hu => h hu)

/-! ═══ ∀ x ∈ U iff ═══ -/

/-! ═══ Reverse: Rminus(u)=0 ↔ Dminus(X⁻¹u)=0 ═══ -/

/-! ═══ Negative-control witness ═══ -/

def p0 : SubextremalKN where
  M := 2; a := 1; Q := 1
  hM := by norm_num
  hQ := by norm_num
  hSub := by norm_num

def x0 : Fin 2 → ℝ := ![4, Real.pi / 2]

theorem rPlus_p0_lt : rPlus p0 < 4 := by
  unfold rPlus p0; simp only
  have harg : (2 : ℝ) ^ 2 - (1 : ℝ) ^ 2 - (1 : ℝ) ^ 2 = 2 := by ring
  rw [harg]
  have : Real.sqrt 2 < 2 := by
    rw [show (2 : ℝ) = Real.sqrt (2^2) from (Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)).symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  linarith

theorem x0_mem : x0 ∈ U p0 := by
  refine ⟨rPlus_p0_lt, ?_, ?_⟩
  · show (0 : ℝ) < (![4, Real.pi / 2] : Fin 2 → ℝ) 1
    simp [Matrix.cons_val_one, Matrix.head_cons]; positivity
  · show (![4, Real.pi / 2] : Fin 2 → ℝ) 1 < Real.pi
    simp [Matrix.cons_val_one, Matrix.head_cons]; linarith [Real.pi_pos]

/-! ═══ Axiom audit ═══ -/




end Hintz2026

end


