-- Prove2me | Definitions.Def_Hintz2026_System1
-- name    : Hintz2026_System1
-- status  : Definition
-- author  : @He Wang
-- created : 2026-10-19T15:50:45.39438+00:00
-- url     : https://prove2.me/theorems/85fb5e2b-11ad-4922-91cf-10b499524a30
-- title:
--   Hintz2026 — System (1), chiral variables (3), and prefactor calculus
-- statement:
--   Throughout, $(M,a,Q)$ is a subextremal Kerr–Newman background ($M>0$, $Q\neq 0$, $a^2+Q^2<M^2$), $\Delta=r^2-2Mr+a^2+Q^2$, $\bar\rho=r+ia\cos\theta$, $\bar\rho^*=r-ia\cos\theta$, $U=\{r>r_+,\ 0<\theta<\pi\}$, and $D^-=\sqrt{\Delta}\,\partial_r-i\,\partial_\theta,\quad D^+=\sqrt{\Delta}\,\partial_r+i\,\partial_\theta$ act through coordinate-slice derivatives; the mode parameters are $\omega,m\in\mathbb{R}$. This bundle transcribes the positive-spin first-order system (1a)–(1d) of Hintz — the operators $\mathcal D_j=\partial_r+iK/\Delta+j\Delta'/\Delta$, $\mathcal L_j=\partial_\theta+\hat Q+j\cot\theta$ and their daggers, the coupling coefficients $F_\pm=3(M-Q^2/\bar\rho)\pm Q^2\bar\rho^*/\bar\rho^2$, and the four residuals `res1a`…`res1d` (left side minus right side) — together with the negative-spin system obtained by the replacement rules ($\psi_1\to-\psi_{-1}$, $\psi_2\to\psi_{-2}$, $k\to-n$, $s\to\ell$, $\mathcal L_{-1}^\dagger\to\mathcal L_{-1}$, $\mathcal L_2\to\mathcal L_2^\dagger$, $(\mathcal D_0+3/\bar\rho^*)\to\Delta(\mathcal D_{-1}^\dagger+3/\bar\rho^*)$, $\Delta(\mathcal D_2^\dagger-3/\bar\rho^*)\to(\mathcal D_0-3/\bar\rho^*)$), residuals `res1aN`…`res1dN`. It defines the chiral variables of eq. (3), $y_\pm^{(+)}=\Delta^{5/4}\sqrt{\sin\theta}\,(\psi_2\pm i\Delta^{-1/2}\psi_1,\,-2Q(k\pm i\Delta^{-1/2}s))$ and $y_\pm^{(-)}=\Delta^{-3/4}\sqrt{\sin\theta}\,(\psi_{-2}\mp i\Delta^{1/2}\psi_{-1},\,2Q(n\mp i\Delta^{1/2}\ell))$, and proves the slice-derivative calculus of the prefactors: $D^\pm(\Delta^{5/4}\sqrt{\sin\theta})=\Delta^{5/4}\sqrt{\sin\theta}\,(\tfrac54\Delta'/\sqrt{\Delta}\pm\tfrac i2\cot\theta)$ and likewise with exponent $-3/4$, plus the product rules $D^\pm(\mathrm{pre}\cdot g)=\mathrm{pre}\,(\lambda g+D^\pm g)$.
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eqs (1a)-(1d), the negative-spin replacement rules, eq. (3); local source Atlas/Perturbations/Hintz2026/{System1Defs,Prefactors,Chiral}.lean at commit aa3cc58 (no public Git remote)

import Definitions.Def_Hintz2026_System4

/-!
# Hintz 2026 — System (1), chiral variables (3), and the prefactor calculus

Source: Hintz, Perturbations of Kerr–Newman black holes: separation and mode stability,
arXiv:2609.33661v1, eqs (1a)–(1d) (positive-spin system, operators 𝒟_j, ℒ_j, their daggers, coupling
coefficients F±), the negative-spin replacement rules, and eq. (3) (chiral variables with prefactors
Δ^{5/4}√sinθ and Δ^{-3/4}√sinθ).  Local source: Atlas/Perturbations/Hintz2026/{System1Defs,Prefactors,Chiral}.lean
at commit aa3cc58.  Definitions, the residual functions of (1), and the slice-derivative calculus of the
prefactors (D± of the prefactors in closed form); the theorems of the block are separate platform nodes.
-/

open Complex Function Matrix
open scoped ComplexConjugate ContDiff

noncomputable section

namespace Hintz2026

variable (p : SubextremalKN)

-- ═══ from System1Defs.lean ═══

def Qhat (om mm : ℝ) (θ : ℝ) : ℝ := -p.a * om * Real.sin θ + mm / Real.sin θ

def cotR (θ : ℝ) : ℝ := Real.cos θ / Real.sin θ

def Fplus (x : Fin 2 -> ℝ) : ℂ :=
  3 * (↑p.M - ↑(p.Q ^ 2) / rhoBar p x) + ↑(p.Q ^ 2) * rhoBarStar p x / rhoBar p x ^ 2

def Fminus (x : Fin 2 -> ℝ) : ℂ :=
  3 * (↑p.M - ↑(p.Q ^ 2) / rhoBar p x) - ↑(p.Q ^ 2) * rhoBarStar p x / rhoBar p x ^ 2

def Dop (j : ℝ) (om mm : ℝ) (f : (Fin 2 -> ℝ) -> ℂ) (x : Fin 2 -> ℝ) : ℂ :=
  cpd 0 f x + (I * ↑(Kfreq p om mm (x 0)) / ↑(Del p (x 0)) + ↑j * ↑(Del' p (x 0)) / ↑(Del p (x 0))) * f x

def DopDag (j : ℝ) (om mm : ℝ) (f : (Fin 2 -> ℝ) -> ℂ) (x : Fin 2 -> ℝ) : ℂ :=
  cpd 0 f x + (-(I * ↑(Kfreq p om mm (x 0)) / ↑(Del p (x 0))) + ↑j * ↑(Del' p (x 0)) / ↑(Del p (x 0))) * f x

def Lop (j : ℝ) (om mm : ℝ) (f : (Fin 2 -> ℝ) -> ℂ) (x : Fin 2 -> ℝ) : ℂ :=
  cpd 1 f x + (↑(Qhat p om mm (x 1)) + ↑j * ↑(cotR (x 1))) * f x

def LopDag (j : ℝ) (om mm : ℝ) (f : (Fin 2 -> ℝ) -> ℂ) (x : Fin 2 -> ℝ) : ℂ :=
  cpd 1 f x + (-↑(Qhat p om mm (x 1)) + ↑j * ↑(cotR (x 1))) * f x

def threeIaSin (x : Fin 2 -> ℝ) : ℂ := 3 * I * ↑(p.a * Real.sin (x 1)) / rhoBarStar p x

def threeOverRhoStar (x : Fin 2 -> ℝ) : ℂ := 3 / rhoBarStar p x

structure PosFields where
  psi2 : (Fin 2 -> ℝ) -> ℂ
  psi1 : (Fin 2 -> ℝ) -> ℂ
  k    : (Fin 2 -> ℝ) -> ℂ
  s    : (Fin 2 -> ℝ) -> ℂ

def res1a (om mm : ℝ) (F : PosFields) (x : Fin 2 -> ℝ) : ℂ :=
  (Lop p 2 om mm F.psi2 x - threeIaSin p x * F.psi2 x)
  - (Dop p 0 om mm F.psi1 x + threeOverRhoStar p x * F.psi1 x)
  + 2 * F.k x * Fplus p x

def res1b (om mm : ℝ) (F : PosFields) (x : Fin 2 -> ℝ) : ℂ :=
  ↑(Del p (x 0)) * (DopDag p 2 om mm F.psi2 x - threeOverRhoStar p x * F.psi2 x)
  + (LopDag p (-1) om mm F.psi1 x + threeIaSin p x * F.psi1 x)
  - 2 * F.s x * Fminus p x

def res1c (om mm : ℝ) (F : PosFields) (x : Fin 2 -> ℝ) : ℂ :=
  (Dop p 0 om mm F.s x + threeOverRhoStar p x * F.s x)
  - (LopDag p (-1) om mm F.k x + threeIaSin p x * F.k x)
  - rhoBar p x / rhoBarStar p x ^ 2 * F.psi2 x

def res1d (om mm : ℝ) (F : PosFields) (x : Fin 2 -> ℝ) : ℂ :=
  ↑(Del p (x 0)) * (DopDag p 2 om mm F.k x - threeOverRhoStar p x * F.k x)
  + (Lop p 2 om mm F.s x - threeIaSin p x * F.s x)
  - 2 * rhoBar p x / rhoBarStar p x ^ 2 * F.psi1 x

structure NegFields where
  psim2 : (Fin 2 -> ℝ) -> ℂ
  psim1 : (Fin 2 -> ℝ) -> ℂ
  n     : (Fin 2 -> ℝ) -> ℂ
  l     : (Fin 2 -> ℝ) -> ℂ

def res1aN (om mm : ℝ) (G : NegFields) (x : Fin 2 -> ℝ) : ℂ :=
  (LopDag p 2 om mm G.psim2 x - threeIaSin p x * G.psim2 x)
  - ↑(Del p (x 0)) * (DopDag p (-1) om mm (fun z => -G.psim1 z) x + threeOverRhoStar p x * (-G.psim1 x))
  + 2 * (-G.n x) * Fplus p x

def res1bN (om mm : ℝ) (G : NegFields) (x : Fin 2 -> ℝ) : ℂ :=
  (Dop p 0 om mm G.psim2 x - threeOverRhoStar p x * G.psim2 x)
  + (Lop p (-1) om mm (fun z => -G.psim1 z) x + threeIaSin p x * (-G.psim1 x))
  - 2 * G.l x * Fminus p x

def res1cN (om mm : ℝ) (G : NegFields) (x : Fin 2 -> ℝ) : ℂ :=
  ↑(Del p (x 0)) * (DopDag p (-1) om mm G.l x + threeOverRhoStar p x * G.l x)
  - (Lop p (-1) om mm (fun z => -G.n z) x + threeIaSin p x * (-G.n x))
  - rhoBar p x / rhoBarStar p x ^ 2 * G.psim2 x

def res1dN (om mm : ℝ) (G : NegFields) (x : Fin 2 -> ℝ) : ℂ :=
  (Dop p 0 om mm (fun z => -G.n z) x - threeOverRhoStar p x * (-G.n x))
  + (LopDag p 2 om mm G.l x - threeIaSin p x * G.l x)
  - 2 * rhoBar p x / rhoBarStar p x ^ 2 * (-G.psim1 x)

def prePos (x : Fin 2 -> ℝ) : ℝ := Real.rpow (Del p (x 0)) (5/4) * Real.sqrt (Real.sin (x 1))

def preNeg (x : Fin 2 -> ℝ) : ℝ := Real.rpow (Del p (x 0)) (-3/4) * Real.sqrt (Real.sin (x 1))

def yPos (e : ℝ) (F : PosFields) (x : Fin 2 -> ℝ) : Fin 2 -> ℂ :=
  ![ ↑(prePos p x) * (F.psi2 x + ↑e * I * F.psi1 x / ↑(Real.sqrt (Del p (x 0)))),
     ↑(prePos p x) * (-2 * ↑p.Q * (F.k x + ↑e * I * F.s x / ↑(Real.sqrt (Del p (x 0))))) ]

def yNeg (e : ℝ) (G : NegFields) (x : Fin 2 -> ℝ) : Fin 2 -> ℂ :=
  ![ ↑(preNeg p x) * (G.psim2 x - ↑e * I * ↑(Real.sqrt (Del p (x 0))) * G.psim1 x),
     ↑(preNeg p x) * (2 * ↑p.Q * (G.n x - ↑e * I * ↑(Real.sqrt (Del p (x 0))) * G.l x)) ]


-- ═══ from Prefactors.lean ═══

theorem hasDerivAt_rpow_Del (q : ℝ) {r : ℝ} (hD : 0 < Del p r) :
    HasDerivAt (fun u => Real.rpow (Del p u) q) (q * Real.rpow (Del p r) (q - 1) * Del' p r) r := by
  have h := (Real.hasDerivAt_rpow_const (p := q) (Or.inl hD.ne')).comp r (hasDerivAt_Del_r p r)
  refine h.congr_deriv ?_
  rw [Del'_eq]; simp only [Real.rpow_eq_pow]; try ring

theorem hasDerivAt_sqrt_sin {θ : ℝ} (hs : 0 < Real.sin θ) :
    HasDerivAt (fun u => Real.sqrt (Real.sin u)) (Real.cos θ / (2 * Real.sqrt (Real.sin θ))) θ := by
  have h := (Real.hasDerivAt_sqrt hs.ne').comp θ (Real.hasDerivAt_sin θ)
  exact h.congr_deriv (by ring)

theorem hasDerivAt_prePos_r (x : Fin 2 -> ℝ) (hD : 0 < Del p (x 0)) :
    HasDerivAt (fun u => prePos p (Function.update x 0 u))
      ((5/4) * Real.rpow (Del p (x 0)) (5/4 - 1) * Del' p (x 0) * Real.sqrt (Real.sin (x 1))) (x 0) := by
  have h := (hasDerivAt_rpow_Del p (5/4) hD).mul_const (Real.sqrt (Real.sin (x 1)))
  refine h.congr_of_eventuallyEq ?_
  filter_upwards with u
  simp [prePos, Function.update, show (1 : Fin 2) ≠ 0 from by decide]

theorem hasDerivAt_prePos_th (x : Fin 2 -> ℝ) (hs : 0 < Real.sin (x 1)) :
    HasDerivAt (fun u => prePos p (Function.update x 1 u))
      (Real.rpow (Del p (x 0)) (5/4) * (Real.cos (x 1) / (2 * Real.sqrt (Real.sin (x 1))))) (x 1) := by
  have h := (hasDerivAt_sqrt_sin hs).const_mul (Real.rpow (Del p (x 0)) (5/4))
  refine h.congr_of_eventuallyEq ?_
  filter_upwards with u
  simp [prePos, Function.update, show (0 : Fin 2) ≠ 1 from by decide]

theorem hasDerivAt_preNeg_r (x : Fin 2 -> ℝ) (hD : 0 < Del p (x 0)) :
    HasDerivAt (fun u => preNeg p (Function.update x 0 u))
      ((-3/4) * Real.rpow (Del p (x 0)) (-3/4 - 1) * Del' p (x 0) * Real.sqrt (Real.sin (x 1))) (x 0) := by
  have h := (hasDerivAt_rpow_Del p (-3/4) hD).mul_const (Real.sqrt (Real.sin (x 1)))
  refine h.congr_of_eventuallyEq ?_
  filter_upwards with u
  simp [preNeg, Function.update, show (1 : Fin 2) ≠ 0 from by decide]

theorem hasDerivAt_preNeg_th (x : Fin 2 -> ℝ) (hs : 0 < Real.sin (x 1)) :
    HasDerivAt (fun u => preNeg p (Function.update x 1 u))
      (Real.rpow (Del p (x 0)) (-3/4) * (Real.cos (x 1) / (2 * Real.sqrt (Real.sin (x 1))))) (x 1) := by
  have h := (hasDerivAt_sqrt_sin hs).const_mul (Real.rpow (Del p (x 0)) (-3/4))
  refine h.congr_of_eventuallyEq ?_
  filter_upwards with u
  simp [preNeg, Function.update, show (0 : Fin 2) ≠ 1 from by decide]

theorem rpow_Del_mul_rpow {r : ℝ} (hD : 0 < Del p r) (a b : ℝ) :
    Real.rpow (Del p r) a * Real.rpow (Del p r) b = Real.rpow (Del p r) (a + b) :=
  (Real.rpow_add hD a b).symm

theorem sqrt_Del_eq_rpow {r : ℝ} (_hD : 0 < Del p r) :
    Real.sqrt (Del p r) = Real.rpow (Del p r) (1/2) := by
  rw [Real.sqrt_eq_rpow]; rfl


-- ═══ from Chiral.lean ═══

theorem prePos_pos {x : Fin 2 -> ℝ} (hx : x ∈ U p) : 0 < prePos p x := by
  unfold prePos
  exact mul_pos (Real.rpow_pos_of_pos (Del_pos p hx.1) _) (Real.sqrt_pos.mpr (sin_pos_of_mem p hx))

theorem preNeg_pos {x : Fin 2 -> ℝ} (hx : x ∈ U p) : 0 < preNeg p x := by
  unfold preNeg
  exact mul_pos (Real.rpow_pos_of_pos (Del_pos p hx.1) _) (Real.sqrt_pos.mpr (sin_pos_of_mem p hx))

theorem cpd0_prePos {x : Fin 2 -> ℝ} (hx : x ∈ U p) :
    cpd 0 (fun z => (↑(prePos p z) : ℂ)) x =
      ↑((5/4) * Real.rpow (Del p (x 0)) (5/4 - 1) * Del' p (x 0) * Real.sqrt (Real.sin (x 1))) := by
  unfold cpd
  exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (x 0) (hasDerivAt_prePos_r p x (Del_pos p hx.1))).deriv

theorem cpd1_prePos {x : Fin 2 -> ℝ} (hx : x ∈ U p) :
    cpd 1 (fun z => (↑(prePos p z) : ℂ)) x =
      ↑(Real.rpow (Del p (x 0)) (5/4) * (Real.cos (x 1) / (2 * Real.sqrt (Real.sin (x 1))))) := by
  unfold cpd
  exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (x 1) (hasDerivAt_prePos_th p x (sin_pos_of_mem p hx))).deriv

theorem cpd0_preNeg {x : Fin 2 -> ℝ} (hx : x ∈ U p) :
    cpd 0 (fun z => (↑(preNeg p z) : ℂ)) x =
      ↑((-3/4) * Real.rpow (Del p (x 0)) (-3/4 - 1) * Del' p (x 0) * Real.sqrt (Real.sin (x 1))) := by
  unfold cpd
  exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (x 0) (hasDerivAt_preNeg_r p x (Del_pos p hx.1))).deriv

theorem cpd1_preNeg {x : Fin 2 -> ℝ} (hx : x ∈ U p) :
    cpd 1 (fun z => (↑(preNeg p z) : ℂ)) x =
      ↑(Real.rpow (Del p (x 0)) (-3/4) * (Real.cos (x 1) / (2 * Real.sqrt (Real.sin (x 1))))) := by
  unfold cpd
  exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (x 1) (hasDerivAt_preNeg_th p x (sin_pos_of_mem p hx))).deriv

def lamPosM (x : Fin 2 -> ℝ) : ℂ := ↑(5/4 * Del' p (x 0) / Real.sqrt (Del p (x 0))) - I / 2 * ↑(cotR (x 1))

def lamPosP (x : Fin 2 -> ℝ) : ℂ := ↑(5/4 * Del' p (x 0) / Real.sqrt (Del p (x 0))) + I / 2 * ↑(cotR (x 1))

def lamNegM (x : Fin 2 -> ℝ) : ℂ := ↑(-3/4 * Del' p (x 0) / Real.sqrt (Del p (x 0))) - I / 2 * ↑(cotR (x 1))

def lamNegP (x : Fin 2 -> ℝ) : ℂ := ↑(-3/4 * Del' p (x 0) / Real.sqrt (Del p (x 0))) + I / 2 * ↑(cotR (x 1))

theorem pre_r_key (q c : ℝ) {x : Fin 2 -> ℝ} (hx : x ∈ U p) :
    Real.sqrt (Del p (x 0)) * (c * Real.rpow (Del p (x 0)) (q - 1) * Del' p (x 0) * Real.sqrt (Real.sin (x 1)))
      = (Real.rpow (Del p (x 0)) q * Real.sqrt (Real.sin (x 1))) * (c * Del' p (x 0) / Real.sqrt (Del p (x 0))) := by
  have hD := Del_pos p hx.1
  have hsD : Real.sqrt (Del p (x 0)) ≠ 0 := (Real.sqrt_pos.mpr hD).ne'
  have hs2 : Real.sqrt (Del p (x 0)) ^ 2 = Del p (x 0) := Real.sq_sqrt hD.le
  have hP1 : Del p (x 0) ^ (q - 1) = Del p (x 0) ^ q / Del p (x 0) := Real.rpow_sub_one hD.ne' _
  simp only [Real.rpow_eq_pow]
  rw [hP1]
  generalize Del p (x 0) ^ q = P
  generalize hsd : Real.sqrt (Del p (x 0)) = s at hs2 hsD ⊢
  generalize Del p (x 0) = D at hs2 ⊢
  subst hs2
  field_simp
  try ring

theorem pre_th_key (q : ℝ) {x : Fin 2 -> ℝ} (hx : x ∈ U p) :
    Real.rpow (Del p (x 0)) q * (Real.cos (x 1) / (2 * Real.sqrt (Real.sin (x 1))))
      = (Real.rpow (Del p (x 0)) q * Real.sqrt (Real.sin (x 1))) * (cotR (x 1) / 2) := by
  have hs := sin_pos_of_mem p hx
  have ht : Real.sqrt (Real.sin (x 1)) ≠ 0 := (Real.sqrt_pos.mpr hs).ne'
  have ht2 : Real.sqrt (Real.sin (x 1)) ^ 2 = Real.sin (x 1) := Real.sq_sqrt hs.le
  unfold cotR
  generalize Real.rpow (Del p (x 0)) q = P
  generalize htd : Real.sqrt (Real.sin (x 1)) = t at ht2 ht ⊢
  generalize Real.sin (x 1) = S at ht2 ⊢
  subst ht2
  field_simp
  try ring

theorem Dm_prePos {x : Fin 2 -> ℝ} (hx : x ∈ U p) :
    Dm p (fun z => (↑(prePos p z) : ℂ)) x = ↑(prePos p x) * lamPosM p x := by
  unfold Dm lamPosM
  rw [cpd0_prePos p hx, cpd1_prePos p hx]
  have e1 : (↑(Real.sqrt (Del p (x 0))) : ℂ) * ↑(5/4 * Real.rpow (Del p (x 0)) (5/4 - 1) * Del' p (x 0) * Real.sqrt (Real.sin (x 1)))
      = ↑(prePos p x) * ↑(5/4 * Del' p (x 0) / Real.sqrt (Del p (x 0))) := by
    rw [← Complex.ofReal_mul, pre_r_key p (5/4) (5/4) hx, Complex.ofReal_mul]; rfl
  have e2 : (↑(Real.rpow (Del p (x 0)) (5/4) * (Real.cos (x 1) / (2 * Real.sqrt (Real.sin (x 1))))) : ℂ)
      = ↑(prePos p x) * ↑(cotR (x 1) / 2) := by
    rw [pre_th_key p (5/4) hx, Complex.ofReal_mul]; rfl
  rw [e1, e2]; push_cast; ring

theorem Dp_prePos {x : Fin 2 -> ℝ} (hx : x ∈ U p) :
    Dp p (fun z => (↑(prePos p z) : ℂ)) x = ↑(prePos p x) * lamPosP p x := by
  unfold Dp lamPosP
  rw [cpd0_prePos p hx, cpd1_prePos p hx]
  have e1 : (↑(Real.sqrt (Del p (x 0))) : ℂ) * ↑(5/4 * Real.rpow (Del p (x 0)) (5/4 - 1) * Del' p (x 0) * Real.sqrt (Real.sin (x 1)))
      = ↑(prePos p x) * ↑(5/4 * Del' p (x 0) / Real.sqrt (Del p (x 0))) := by
    rw [← Complex.ofReal_mul, pre_r_key p (5/4) (5/4) hx, Complex.ofReal_mul]; rfl
  have e2 : (↑(Real.rpow (Del p (x 0)) (5/4) * (Real.cos (x 1) / (2 * Real.sqrt (Real.sin (x 1))))) : ℂ)
      = ↑(prePos p x) * ↑(cotR (x 1) / 2) := by
    rw [pre_th_key p (5/4) hx, Complex.ofReal_mul]; rfl
  rw [e1, e2]; push_cast; ring

theorem Dm_preNeg {x : Fin 2 -> ℝ} (hx : x ∈ U p) :
    Dm p (fun z => (↑(preNeg p z) : ℂ)) x = ↑(preNeg p x) * lamNegM p x := by
  unfold Dm lamNegM
  rw [cpd0_preNeg p hx, cpd1_preNeg p hx]
  have e1 : (↑(Real.sqrt (Del p (x 0))) : ℂ) * ↑(-3/4 * Real.rpow (Del p (x 0)) (-3/4 - 1) * Del' p (x 0) * Real.sqrt (Real.sin (x 1)))
      = ↑(preNeg p x) * ↑(-3/4 * Del' p (x 0) / Real.sqrt (Del p (x 0))) := by
    rw [← Complex.ofReal_mul, pre_r_key p (-3/4) (-3/4) hx, Complex.ofReal_mul]; rfl
  have e2 : (↑(Real.rpow (Del p (x 0)) (-3/4) * (Real.cos (x 1) / (2 * Real.sqrt (Real.sin (x 1))))) : ℂ)
      = ↑(preNeg p x) * ↑(cotR (x 1) / 2) := by
    rw [pre_th_key p (-3/4) hx, Complex.ofReal_mul]; rfl
  rw [e1, e2]; push_cast; ring

theorem Dp_preNeg {x : Fin 2 -> ℝ} (hx : x ∈ U p) :
    Dp p (fun z => (↑(preNeg p z) : ℂ)) x = ↑(preNeg p x) * lamNegP p x := by
  unfold Dp lamNegP
  rw [cpd0_preNeg p hx, cpd1_preNeg p hx]
  have e1 : (↑(Real.sqrt (Del p (x 0))) : ℂ) * ↑(-3/4 * Real.rpow (Del p (x 0)) (-3/4 - 1) * Del' p (x 0) * Real.sqrt (Real.sin (x 1)))
      = ↑(preNeg p x) * ↑(-3/4 * Del' p (x 0) / Real.sqrt (Del p (x 0))) := by
    rw [← Complex.ofReal_mul, pre_r_key p (-3/4) (-3/4) hx, Complex.ofReal_mul]; rfl
  have e2 : (↑(Real.rpow (Del p (x 0)) (-3/4) * (Real.cos (x 1) / (2 * Real.sqrt (Real.sin (x 1))))) : ℂ)
      = ↑(preNeg p x) * ↑(cotR (x 1) / 2) := by
    rw [pre_th_key p (-3/4) hx, Complex.ofReal_mul]; rfl
  rw [e1, e2]; push_cast; ring

theorem diff_prePos_slice {x : Fin 2 -> ℝ} (hx : x ∈ U p) (k : Fin 2) :
    DifferentiableAt ℝ (fun u => (↑(prePos p (update x k u)) : ℂ)) (x k) := by
  fin_cases k
  · exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (x 0) (hasDerivAt_prePos_r p x (Del_pos p hx.1))).differentiableAt
  · exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (x 1) (hasDerivAt_prePos_th p x (sin_pos_of_mem p hx))).differentiableAt

theorem diff_preNeg_slice {x : Fin 2 -> ℝ} (hx : x ∈ U p) (k : Fin 2) :
    DifferentiableAt ℝ (fun u => (↑(preNeg p (update x k u)) : ℂ)) (x k) := by
  fin_cases k
  · exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (x 0) (hasDerivAt_preNeg_r p x (Del_pos p hx.1))).differentiableAt
  · exact (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt (x 1) (hasDerivAt_preNeg_th p x (sin_pos_of_mem p hx))).differentiableAt

theorem Dm_prePos_mul {x : Fin 2 -> ℝ} (hx : x ∈ U p) (g : (Fin 2 -> ℝ) -> ℂ)
    (hg : ∀ k, DifferentiableAt ℝ (fun u => g (update x k u)) (x k)) :
    Dm p (fun z => ↑(prePos p z) * g z) x = ↑(prePos p x) * (lamPosM p x * g x + Dm p g x) := by
  rw [Dm_mul p _ g x (diff_prePos_slice p hx 0) (hg 0) (diff_prePos_slice p hx 1) (hg 1), Dm_prePos p hx]; ring

theorem Dp_prePos_mul {x : Fin 2 -> ℝ} (hx : x ∈ U p) (g : (Fin 2 -> ℝ) -> ℂ)
    (hg : ∀ k, DifferentiableAt ℝ (fun u => g (update x k u)) (x k)) :
    Dp p (fun z => ↑(prePos p z) * g z) x = ↑(prePos p x) * (lamPosP p x * g x + Dp p g x) := by
  rw [Dp_mul p _ g x (diff_prePos_slice p hx 0) (hg 0) (diff_prePos_slice p hx 1) (hg 1), Dp_prePos p hx]; ring

theorem Dm_preNeg_mul {x : Fin 2 -> ℝ} (hx : x ∈ U p) (g : (Fin 2 -> ℝ) -> ℂ)
    (hg : ∀ k, DifferentiableAt ℝ (fun u => g (update x k u)) (x k)) :
    Dm p (fun z => ↑(preNeg p z) * g z) x = ↑(preNeg p x) * (lamNegM p x * g x + Dm p g x) := by
  rw [Dm_mul p _ g x (diff_preNeg_slice p hx 0) (hg 0) (diff_preNeg_slice p hx 1) (hg 1), Dm_preNeg p hx]; ring

theorem Dp_preNeg_mul {x : Fin 2 -> ℝ} (hx : x ∈ U p) (g : (Fin 2 -> ℝ) -> ℂ)
    (hg : ∀ k, DifferentiableAt ℝ (fun u => g (update x k u)) (x k)) :
    Dp p (fun z => ↑(preNeg p z) * g z) x = ↑(preNeg p x) * (lamNegP p x * g x + Dp p g x) := by
  rw [Dp_mul p _ g x (diff_preNeg_slice p hx 0) (hg 0) (diff_preNeg_slice p hx 1) (hg 1), Dp_preNeg p hx]; ring

end Hintz2026

end


