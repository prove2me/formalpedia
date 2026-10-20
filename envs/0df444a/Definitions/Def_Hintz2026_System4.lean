-- Prove2me | Definitions.Def_Hintz2026_System4
-- name    : Hintz2026_System4
-- status  : Definition
-- author  : @He Wang
-- created : 2026-10-19T14:51:47.61772+00:00
-- url     : https://prove2.me/theorems/9c350beb-d791-4956-988e-fdbd2cb91951
-- title:
--   Hintz2026 — system (4) coefficients, transformation (7), separated coefficients R, Θ
-- statement:
--   Explicit coefficient data of Hintz's chiral first-order system (4) and of the transformation (7), on the domain $U=\{r>r_+,\ 0<\theta<\pi\}$ of a subextremal Kerr–Newman background: the mode functions $K = -(r^2+a^2)\omega + am$ and $\Delta' = 2(r-M)$; the traceless matrix $B^{(\varsigma)} = i\begin{pmatrix} b & 3(M\bar\rho - Q^2)/(Q\bar\rho) \\ 3Q\bar\rho/\bar\rho^{*2} & -b\end{pmatrix}$ with $b = -\varsigma\hat Q - \tfrac32\cot\theta + 3ia\sin\theta/\bar\rho^*$, $\hat Q = -a\omega\sin\theta + m/\sin\theta$; the scalar $c^{(\varsigma)} = \bigl(\varsigma\tfrac{iK}{\Delta} + \tfrac{3}{\bar\rho^*} - \tfrac{3\Delta'}{4\Delta}\bigr)\sqrt\Delta$; the transformed fields $z_+ = \operatorname{adj}(X)\,y_+$ (equal to $(\det X)X^{-1}y_+$ since $\det X = Q^2-M^2$ is constant) and $z_- = X^*y_-$; the coupling matrix $C^{(\varsigma)} = (\det X)X^{-1}(c^{(\varsigma)}I - B^{(\varsigma)})(X^*)^{-1}$; the independent explicit coefficients $R_0, R_1, \Theta_0, \Theta_1$ written after eq. (7) and the matrices $R^{(\varsigma)}(r) = \begin{pmatrix} R_0 & R_1 \\ -R_1 & R_0\end{pmatrix}$, $\Theta^{(\varsigma)}(\theta) = \begin{pmatrix} \Theta_0 & \Theta_1 \\ \Theta_1 & -\Theta_0\end{pmatrix}$, $C_{\mathrm{sep}} = R(r) + i\Theta(\theta)$; and the block scaffolding $J$, the angular multiplication block associated with eq. (8), and $R_0 I+R_1J=R^{\mathsf T}$ (the lower-left radial block, not $R$ itself). These scaffolding definitions are not a separately proved full four-component operator equivalence. The spin parameter $\varsigma$ is a real parameter; the paper's two spin directions are $\varsigma = \pm 1$; $\omega, m$ are real. Short structural lemmas included: $\operatorname{tr}B = 0$; $\det X \neq 0$; the round trips $X z_+ = (\det X)\,y_+$, $(X^*)^{-1}z_- = y_-$; $\operatorname{adj}X = (Q^2-M^2)X^{-1}$; $(X^*)^{-1} = (Q^2-M^2)^{-1}\operatorname{adj}(X)^*$; $\operatorname{adj}(cI - B) = cI + B$ for traceless $B$; $\operatorname{adj}(M^{-1}) = (\det M)^{-1}M$ for an invertible $2\times2$ complex matrix $M$ (here $M$ denotes a matrix, not the mass).
-- source:
--   Hintz, Perturbations of Kerr-Newman black holes: separation and mode stability, arXiv:2609.33661v1, Section 2 eq. (4), eq. (7), the text after (7), eq. (8); local source Atlas/Perturbations/Hintz2026/{System4Defs,Transform7,CSeparation,AdjDeriv,CAdjugate,System8}.lean at commit 8d059e0 (no public Git remote)

import Definitions.Def_Hintz2026_AnalysisV2

/-!
# Hintz 2026 — System (4) coefficients, transformation (7), and the separated form

Source: Hintz, Perturbations of Kerr–Newman black holes: separation and mode stability,
arXiv:2609.33661v1, eq. (4) (matrix `B`, scalar `c`), eq. (7) (`z±`, `C`), the text after (7)
(coefficients `R₀, R₁, Θ₀, Θ₁` of `C = R(r) + iΘ(θ)`), eq. (8) (block matrices).
Local source: Atlas/Perturbations/Hintz2026/{System4Defs,Transform7,CSeparation,AdjDeriv,CAdjugate,System8}.lean
at commit 8d059e0.  Only definitions and short structural lemmas; the theorems of the block are
separate platform nodes.
-/

open Complex Matrix Function
open scoped ComplexConjugate

noncomputable section

namespace Hintz2026

variable (p : SubextremalKN)

-- ═══ from System4Defs.lean ═══

def Kfreq (ω m : ℝ) (r : ℝ) : ℝ := -(r ^ 2 + p.a ^ 2) * ω + p.a * m

def Del' (r : ℝ) : ℝ := 2 * (r - p.M)

theorem Del'_eq (r : ℝ) : Del' p r = 2 * r - 2 * p.M := by unfold Del'; ring

def bcoeff (ς ω m : ℝ) (x : Fin 2 → ℝ) : ℂ :=
  -↑ς * ↑(-p.a * ω * Real.sin (x 1) + m / Real.sin (x 1))
  - ↑(3 / 2 * Real.cos (x 1) / Real.sin (x 1))
  + 3 * Complex.I * ↑(p.a * Real.sin (x 1)) / rhoBarStar p x

def Bmat (ς ω m : ℝ) (x : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Complex.I • !![bcoeff p ς ω m x,
         3 * (↑p.M * rhoBar p x - ↑(p.Q ^ 2)) / (↑p.Q * rhoBar p x);
         3 * ↑p.Q * rhoBar p x / rhoBarStar p x ^ 2,
         -bcoeff p ς ω m x]

def cscalar (ς ω m : ℝ) (x : Fin 2 → ℝ) : ℂ :=
  (↑ς * Complex.I * ↑(Kfreq p ω m (x 0)) / ↑(Del p (x 0))
   + 3 / rhoBarStar p x
   - ↑(3 * Del' p (x 0) / (4 * Del p (x 0))))
  * ↑(Real.sqrt (Del p (x 0)))

theorem Bmat_trace_zero (ς ω m : ℝ) (x : Fin 2 → ℝ) :
    (Bmat p ς ω m x).trace = 0 := by
  unfold Bmat
  simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two, Matrix.smul_apply,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.head_fin_const, smul_eq_mul]


-- ═══ from Transform7.lean ═══

def zplus (yplus : (Fin 2 → ℝ) → Fin 2 → ℂ)
    (x : Fin 2 → ℝ) : Fin 2 → ℂ :=
  adjugate (X p x) *ᵥ yplus x

def zminus (yminus : (Fin 2 → ℝ) → Fin 2 → ℂ)
    (x : Fin 2 → ℝ) : Fin 2 → ℂ :=
  (X p x)ᴴ *ᵥ yminus x

def Cmat (ς ω m : ℝ) (x : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (X p x).det • ((X p x)⁻¹ * (cscalar p ς ω m x • 1 - Bmat p ς ω m x) * ((X p x)ᴴ)⁻¹)

theorem det_ne {x : Fin 2 → ℝ} (hx : x ∈ U p) : (X p x).det ≠ 0 := by
  rw [det_X p hx]; exact_mod_cast Q_sq_sub_M_sq_ne_zero p

theorem X_mulVec_zplus (yplus : (Fin 2 → ℝ) → Fin 2 → ℂ)
    (x : Fin 2 → ℝ) :
    X p x *ᵥ zplus p yplus x = (X p x).det • yplus x := by
  simp only [zplus, mulVec_mulVec, mul_adjugate, smul_mulVec, one_mulVec]

theorem yplus_of_zplus (yplus : (Fin 2 → ℝ) → Fin 2 → ℂ)
    {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    (X p x).det⁻¹ • (X p x *ᵥ zplus p yplus x) = yplus x := by
  rw [X_mulVec_zplus, smul_smul, inv_mul_cancel₀ (det_ne p hx), one_smul]

theorem yminus_of_zminus (yminus : (Fin 2 → ℝ) → Fin 2 → ℂ)
    {x : Fin 2 → ℝ} (hx : x ∈ U p) :
    ((X p x)ᴴ)⁻¹ *ᵥ zminus p yminus x = yminus x := by
  simp only [zminus, mulVec_mulVec, inv_mul_Xstar p hx, one_mulVec]


-- ═══ from CSeparation.lean ═══

private abbrev ofR : ℝ → ℂ := Complex.ofReal

def R0coeff (ς ω m : ℝ) (r : ℝ) : ℂ :=
  ofR (3 * Del' p r / (4 * Real.sqrt (Del p r)))
  - I * ofR ς * ofR (Real.sqrt (Del p r))
    * (ofR (Kfreq p ω m r) / ofR (Del p r)
       - ofR (2 * ω * p.Q ^ 2) / ofR (p.M ^ 2 - p.Q ^ 2))

def R1coeff (ς ω : ℝ) (r : ℝ) : ℂ :=
  -ofR ς * ofR (2 * ω * p.Q * (p.M * r - p.Q ^ 2)) / ofR (p.M ^ 2 - p.Q ^ 2)
  + I * ofR (3 * p.M) / ofR (2 * p.Q)

def Th0coeff (ς ω m : ℝ) (θ : ℝ) : ℝ :=
  3 / 2 * Real.cos θ / Real.sin θ
  + ς * (m / Real.sin θ
    - p.a * ω * (p.M ^ 2 + p.Q ^ 2) * Real.sin θ / (p.M ^ 2 - p.Q ^ 2))

def Th1coeff (ς ω : ℝ) (θ : ℝ) : ℝ :=
  -ς * 2 * p.a * ω * p.M * p.Q * Real.cos θ / (p.M ^ 2 - p.Q ^ 2)
  - 3 * p.M / (2 * p.Q)

def Rmat (ς ω m : ℝ) (r : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![R0coeff p ς ω m r, R1coeff p ς ω r;
     -R1coeff p ς ω r, R0coeff p ς ω m r]

def Thmat (ς ω m : ℝ) (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![ofR (Th0coeff p ς ω m θ), ofR (Th1coeff p ς ω θ);
     ofR (Th1coeff p ς ω θ), -ofR (Th0coeff p ς ω m θ)]

def Csep (ς ω m : ℝ) (x : Fin 2 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Rmat p ς ω m (x 0) + I • Thmat p ς ω m (x 1)


-- ═══ from AdjDeriv.lean ═══

theorem adj_X_eq_const_smul_inv {z : Fin 2 -> ℝ} (hz : z ∈ U p) :
    adjugate (X p z) = ((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ) • (X p z)⁻¹ := by
  rw [← det_X p hz, Matrix.inv_def, smul_smul, Ring.inverse_eq_inv,
    mul_inv_cancel₀ (det_ne p hz), one_smul]

theorem adj_X_entry_eq {z : Fin 2 -> ℝ} (hz : z ∈ U p) (i j : Fin 2) :
    adjugate (X p z) i j = ((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ) * (X p z)⁻¹ i j := by
  rw [adj_X_eq_const_smul_inv p hz, Matrix.smul_apply, smul_eq_mul]


-- ═══ from CAdjugate.lean ═══

theorem detX_Xinv_eq_adj {x : Fin 2 -> ℝ} (hx : x ∈ U p) :
    (X p x).det • (X p x)⁻¹ = adjugate (X p x) := by
  rw [Matrix.inv_def, smul_smul, Ring.inverse_eq_inv, mul_inv_cancel₀ (det_ne p hx), one_smul]

theorem adjugate_cI_sub_B (c : ℂ) (B : Matrix (Fin 2) (Fin 2) ℂ) (htr : B.trace = 0) :
    adjugate (c • (1 : Matrix (Fin 2) (Fin 2) ℂ) - B) = c • 1 + B := by
  rw [adjugate_fin_two]
  simp only [Matrix.trace, Matrix.diag, Fin.sum_univ_two] at htr
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> linear_combination (-1 : ℂ) * htr

theorem adjugate_inv_eq (M : Matrix (Fin 2) (Fin 2) ℂ) (hM : M.det ≠ 0) :
    adjugate M⁻¹ = (M.det)⁻¹ • M := by
  have h1 : M⁻¹.adjugate * M⁻¹ = M⁻¹.det • 1 := adjugate_mul _
  rw [det_nonsing_inv, Ring.inverse_eq_inv] at h1
  have hinv : IsUnit M.det := isUnit_iff_ne_zero.mpr hM
  calc adjugate M⁻¹ = adjugate M⁻¹ * (M⁻¹ * M) := by rw [nonsing_inv_mul _ hinv, Matrix.mul_one]
    _ = (adjugate M⁻¹ * M⁻¹) * M := by rw [Matrix.mul_assoc]
    _ = (M.det⁻¹ • 1) * M := by rw [h1]
    _ = M.det⁻¹ • M := by rw [Matrix.smul_mul, Matrix.one_mul]

theorem Xstar_inv_eq {x : Fin 2 -> ℝ} (hx : x ∈ U p) :
    ((X p x)ᴴ)⁻¹ = (((p.Q ^ 2 - p.M ^ 2 : ℝ) : ℂ))⁻¹ • (adjugate (X p x))ᴴ := by
  rw [Matrix.inv_def, Ring.inverse_eq_inv, det_conjTranspose, det_X p hx, Matrix.adjugate_conjTranspose]
  congr 1
  rw [star_def, conj_ofReal]


-- ═══ from System8.lean ═══

def Jtwo : Matrix (Fin 2) (Fin 2) ℂ := !![0, -1; 1, 0]

def Aang_block (ς ω m : ℝ) (θ : ℝ) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℂ :=
  Matrix.fromBlocks (0 : Matrix (Fin 2) (Fin 2) ℂ) (I • Thmat p ς ω m θ)
    ((-I) • Thmat p ς ω m θ) (0 : Matrix (Fin 2) (Fin 2) ℂ)

def radBlock (ς ω m : ℝ) (r : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  R0coeff p ς ω m r • (1 : Matrix (Fin 2) (Fin 2) ℂ) + R1coeff p ς ω r • Jtwo

end Hintz2026

end


