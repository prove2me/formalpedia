-- Prove2me | Definitions.Def_PrivGaussMS_CandidateDensity
-- name    : PrivGaussMS_CandidateDensity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T04:09:50.22548+00:00
-- url     : https://prove2.me/theorems/d2f63694-f43f-424b-adf8-be8bd2d63e41
-- title:
--   Frame-row density (4), candidate density $f_B^{(r)}$ (20), and $V_Y$ (34)
-- statement:
--   With $c_{N,r,p}=\pi^{-rp/2}\prod_{j=1}^p\Gamma((N-j+1)/2)/\Gamma((N-r-j+1)/2)$, the frame-row density is $c_{N,r,p}\det(I_p-Z^TZ)^{(N-r-p-1)/2}\mathbf 1\{I_p-Z^TZ\succ0\}$. For an $r\times d$ matrix $Y$ put $\tilde Y=[Y,1_r]$, $R_B(Y)=\det(I_r-\tilde YB^{-1}\tilde Y^T)$, $\kappa_r=(n-r-d-2)/2$ and $A_r(b)=b^{(n-2)/2}/(b-r)^{(n-r-2)/2}$. The candidate density is $f_B^{(0)}=1$ and, for $r\ge1$,
--   $$f_B^{(r)}(Y)=c_{n-1,r,d}\,A_r(b)(\det B)^{-r/2}R_B(Y)^{\kappa_r}\quad\text{on }B-\tilde Y^T\tilde Y\succ0,$$
--   and $0$ elsewhere. For $B=\mathrm{diag}(I_d,b)$, $W=[Y,1_m/\sqrt b]$ and $V_Y=W^T(I_m-WW^T)^{-1}W$; $\mathbb EV_Y$ is its entrywise expectation.
--
--   **Formalization Note** Real powers are `Real.rpow`, used only on positive bases (the indicator vanishes elsewhere). Lemma B.4 is the separate statement that $f_B^{(r)}$ is the density of the candidate rows.
-- source:
--   Moayedi, Yassaee, Ebrahimi, Optimal Private Gaussian Multi-sampling, STOC 2027 submission (manuscript sha256 1838c582…), Lemma A.11 eq. (4), p.29; §B.3.4 and Lemma B.4 eq. (20), p.40; §B.6.1, p.55

import Mathlib
import Definitions.Def_PrivGaussMS_Statistics

open MeasureTheory Matrix
open scoped MatrixOrder

namespace PrivGaussMS

/-!
# Frame-block densities (4), candidate densities (20), and `V_Y` (34)

Moayedi, Yassaee, Ebrahimi, *Optimal Private Gaussian Multi-sampling*, STOC 2027 submission
(manuscript sha256 1838c582…), Lemma A.11, eq. (4), p.29; §B.3.4 and Lemma B.4, eq. (20), p.40;
§B.6.1, p.55.

**Formalization Note.**
* `cFrame N r p = π^{−rp/2} Π_{j=1}^{p} Γ((N − j + 1)/2)/Γ((N − r − j + 1)/2)` (4), with `N` real.
* `frameRowDensity N r p Z = c_{N,r,p} det(I_p − ZᵀZ)^{(N−r−p−1)/2} 1{I_p − ZᵀZ ≻ 0}` (4). Powers with
  real exponents are `Real.rpow`, applied only where the base is positive (the indicator is `0`
  elsewhere).
* `Ytil Y = [Y, 1_r]`, `RB B Y = det(I_r − Ỹ B^{−1} Ỹᵀ)`, `kappa n r d = (n − r − d − 2)/2`,
  `Ar n r b = b^{(n−2)/2}/(b − r)^{(n−r−2)/2}` (p.40).
* `candDensity n r B Y = f_B^{(r)}(Y)`: `1` for `r = 0` ("Set `f_B^{(0)} = 1`", p.40); otherwise
  `c_{n−1,r,d} A_r(b) (det B)^{−r/2} R_B(Y)^{κ_r}` on `B − ỸᵀỸ ≻ 0` and `0` outside (20). The
  formula is the paper's; Lemma B.4 is the statement that it is the density.
* `VY n b Y = Wᵀ(I_m − WWᵀ)^{−1}W` with `W = [Y, 1_m/√b]` (p.55); `EVY` its entrywise expectation.
-/

variable {d : ℕ}

/-- `c_{N,r,p} = π^{−rp/2} Π_{j=1}^{p} Γ((N − j + 1)/2)/Γ((N − r − j + 1)/2)` (4). -/
noncomputable def cFrame (N : ℝ) (r p : ℕ) : ℝ :=
  Real.pi ^ (-((r : ℝ) * p) / 2) *
    ∏ j ∈ Finset.Icc 1 p, Real.Gamma ((N - j + 1) / 2) / Real.Gamma ((N - r - j + 1) / 2)

open Classical in
/-- The density (4) of the first `r` rows of a uniform `N × p` frame. -/
noncomputable def frameRowDensity (N : ℝ) (r p : ℕ) (Z : Matrix (Fin r) (Fin p) ℝ) : ℝ :=
  if (1 - Zᵀ * Z).PosDef then cFrame N r p * (1 - Zᵀ * Z).det ^ ((N - r - p - 1) / 2) else 0

/-- `Ỹ = [Y, 1_r]` (p.40). -/
def Ytil {r : ℕ} (Y : Matrix (Fin r) (Fin d) ℝ) : Matrix (Fin r) (Fin (d + 1)) ℝ :=
  fun i => Fin.snoc (α := fun _ => ℝ) (Y i) 1

/-- `R_B(Y) = det(I_r − Ỹ B^{−1} Ỹᵀ)` (p.40). -/
noncomputable def RB {r : ℕ} (B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (Y : Matrix (Fin r) (Fin d) ℝ) : ℝ :=
  (1 - Ytil Y * B⁻¹ * (Ytil Y)ᵀ).det

/-- `κ_r = (n − r − d − 2)/2` (p.40). -/
noncomputable def kappa (n r d : ℕ) : ℝ := ((n : ℝ) - r - d - 2) / 2

/-- `A_r(b) = b^{(n−2)/2}/(b − r)^{(n−r−2)/2}` (20). -/
noncomputable def Ar (n r : ℕ) (b : ℝ) : ℝ :=
  b ^ (((n : ℝ) - 2) / 2) / (b - r) ^ (((n : ℝ) - r - 2) / 2)

open Classical in
/-- The candidate density `f_B^{(r)}` of (20), with `f_B^{(0)} = 1`. -/
noncomputable def candDensity (n r : ℕ) (B : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ)
    (Y : Matrix (Fin r) (Fin d) ℝ) : ℝ :=
  if r = 0 then 1
  else if (B - (Ytil Y)ᵀ * Ytil Y).PosDef then
    cFrame ((n : ℝ) - 1) r d * Ar n r (bw B) * B.det ^ (-(r : ℝ) / 2) *
      RB B Y ^ kappa n r d
  else 0

/-- `diag(I_d, b)` (p.55). -/
def diagIb (d : ℕ) (b : ℝ) : Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  Matrix.diagonal (Fin.snoc (α := fun _ => ℝ) (fun _ => 1) b)

/-- `W = [Y, 1_m/√b] = Ỹ B^{−1/2}` for `B = diag(I_d, b)` (p.55). -/
noncomputable def Wmat {m : ℕ} (b : ℝ) (Y : Matrix (Fin m) (Fin d) ℝ) :
    Matrix (Fin m) (Fin (d + 1)) ℝ :=
  fun i => Fin.snoc (α := fun _ => ℝ) (Y i) (1 / Real.sqrt b)

/-- `V_Y = Wᵀ(I_m − WWᵀ)^{−1} W` (p.55). -/
noncomputable def VY {m : ℕ} (b : ℝ) (Y : Matrix (Fin m) (Fin d) ℝ) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  (Wmat b Y)ᵀ * (1 - Wmat b Y * (Wmat b Y)ᵀ)⁻¹ * Wmat b Y

/-- `E V_Y`, entrywise, under a law `μ` of `Y`. -/
noncomputable def EVY {m : ℕ} (b : ℝ) (μ : Measure (Matrix (Fin m) (Fin d) ℝ)) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) ℝ :=
  fun i j => ∫ Y, VY b Y i j ∂μ

end PrivGaussMS


