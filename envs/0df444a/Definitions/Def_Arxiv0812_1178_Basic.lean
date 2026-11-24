-- Prove2me | Definitions.Def_Arxiv0812_1178_Basic
-- name    : Arxiv0812_1178_Basic
-- status  : Definition
-- author  : @Xeroth
-- created : 2026-11-24T08:45:41.242647+00:00
-- url     : https://prove2.me/theorems/a2973eb9-f301-4474-a823-0087063de9cb
-- title:
--   Baseline and closure operators, pseudo phases, myopic criterion and polar noise components
-- statement:
--   Objects of Sections 2-3 and Appendices A, C and E of Meimon, Mugnier and Le Besnerais (2008).
--
--   1. **Array and baselines.** A complete non-redundant array has $N_t\ge3$ telescopes $T_1,\dots,T_{N_t}$. Its $N_b=N_t(N_t-1)/2$ baselines are the pairs $(k,l)$ with $k<l$. The canonical closure phases are indexed by the $(N_t-1)(N_t-2)/2$ pairs $(k,l)$ with $1<k<l$.
--   2. **Closure phases (eq. 10).** For phases $\phi_{kl}$ on ordered pairs of telescopes, $\beta_{klm}=\phi_{kl}+\phi_{lm}+\phi_{mk}$. The canonical closures are $\beta_{1kl}$, $1<k<l$.
--   3. **Baseline operator (eqs. 37-38).** $B$ is the $N_b\times N_t$ matrix with $(B\varpi)_{kl}=\varpi_l-\varpi_k$. $\bar B$ is $B$ with its first column (telescope $T_1$) removed, an $N_b\times(N_t-1)$ matrix.
--   4. **Closure operator (eq. 39).** $C=[-B_{N_t-1}\mid\mathrm{Id}]$, the matrix with $(C\phi)_{kl}=\phi_{1k}+\phi_{kl}-\phi_{1l}$ for $1<k<l$. Its generalized inverse is $C^\dagger=C^{\mathsf T}(CC^{\mathsf T})^{-1}$.
--   5. **Object phases (eq. 5).** For object coefficients $x\in\mathbb R^P$ and a complex $N_b\times P$ Fourier matrix $H(t)$, $\phi(x,t)=\arg(H(t)x)$ componentwise.
--   6. **Pseudo phases (eqs. 24-25).** $\phi^{data}(t)=C^\dagger\beta^{data}(t)$ and $\phi^{ker}(t)=(C^\dagger C-\mathrm{Id})\phi(x,t)+2\pi C^\dagger\kappa$ for an integer vector $\kappa$.
--   7. **Myopic model and criterion (eqs. 34-35).** $y_m(x,\alpha(t))=H(t)x\cdot e^{i\bar B\alpha(t)}$ (componentwise) with $\alpha(t)\in\mathbb R^{N_t-1}$. With $r=y^{data}(t)-y_m-\bar y^{noise}(t)$, the statistic is $\chi^2_{y(t)}=[\operatorname{Re}r;\operatorname{Im}r]^{\mathsf T}R_{y^{noise}(t)}^{-1}[\operatorname{Re}r;\operatorname{Im}r]$. The criterion is $J^{data}(x,\alpha)=\sum_t\chi^2_{y(t)}(x,\alpha(t))$ over finitely many instants $t$.
--   8. **Polar noise (eqs. 52-54).** For $a^{data}=\bar a+a^{noise}$ and $\phi^{data}=\bar\phi+\phi^{noise}$, set $y^{noise}=a^{data}e^{i\phi^{data}}-\bar ae^{i\bar\phi}$, $y^n_{rad}=\operatorname{Re}(y^{noise}e^{-i\bar\phi})$ and $y^n_{tan}=\operatorname{Im}(y^{noise}e^{-i\bar\phi})$, componentwise.
--
--   **Formalization Note** Telescope $T_1$ is index $0$ of $\mathrm{Fin}\,N_t$. $B$ and $C$ are written entrywise with rows and columns indexed by pairs of telescopes, not by the recursive block layout of eqs. (37)-(39). The two coincide once baselines are ordered lexicographically ($(1,2),(1,3),\dots,(1,N_t),(2,3),\dots$); this was checked for $N_t=3,\dots,8$. Phases are real numbers; "modulo $2\pi$" is written as "up to $2\pi$ times an integer vector". $(CC^{\mathsf T})^{-1}$ is Mathlib's matrix inverse, which is the true inverse because $CC^{\mathsf T}$ is invertible.
-- source:
--   Meimon, Mugnier and Le Besnerais, A self-calibration approach for optical long baseline interferometry imaging, arXiv:0812.1178v1 (2008), Sec. 2.A, 2.C, 3.B, 3.C (eqs. (5), (10), (24)-(25), (34)-(35)), Appendix A (eqs. (37)-(39)), Appendix C, Appendix E.A (eqs. (52)-(54))

import Mathlib

/-!
Meimon, Mugnier and Le Besnerais, *A self-calibration approach for optical long baseline
interferometry imaging*, arXiv:0812.1178v1 (2008): the baselines and closure phases of a complete
array (Sec. 2.A, 2.C), the baseline and closure operators `B`, `C` (Appendix A), the generalized
inverse `C†` and the pseudo-phase data (Sec. 3.B), the myopic model and goodness-of-fit criterion
(Sec. 3.C, eqs. (34)-(35)), and the radial and tangential noise components of a polar Gaussian
model (Appendix E.A, eqs. (52)-(54)).

Telescopes `T_1, …, T_{N_t}` are indexed by `Fin n`, with `T_1` the index `0`.
-/

open Matrix

noncomputable section

namespace Arxiv0812_1178

/-- Sec. 2.A, eq. (4): the `N_b = N_t(N_t-1)/2` baselines `(k,l)`, `k < l`, of a complete
non-redundant array of `n` telescopes. -/
abbrev Baseline (n : ℕ) := {p : Fin n × Fin n // p.1 < p.2}

/-- Sec. 2.C: index set of the canonical closure phases `β_{1kl}`, `1 < k < l` (pairs `(k,l)` of
telescopes other than `T_1`, which is the index `0`). -/
abbrev ClosureIdx (n : ℕ) := {p : Fin n × Fin n // 0 < p.1.1 ∧ p.1 < p.2}

/-- Appendix A, eqs. (37)-(38): the `N_b × N_t` baseline operator `B`, with
`(B ϖ)_{kl} = ϖ_l - ϖ_k` (eqs. (6)-(7)). Rows are indexed by baselines rather than by the recursive
block layout of eq. (38); the two agree after ordering baselines lexicographically. -/
def baselineOp (n : ℕ) : Matrix (Baseline n) (Fin n) ℝ :=
  fun b j => (if j = b.1.2 then 1 else 0) - (if j = b.1.1 then 1 else 0)

/-- Appendix C: `B̄`, the baseline operator with its first column (telescope `T_1`) removed;
column `j` of `B̄` is column `j + 1` of `B`. -/
def baselineOpBar (n : ℕ) : Matrix (Baseline n) (Fin (n - 1)) ℝ :=
  fun b j => baselineOp n b ⟨j.1 + 1, by have := j.2; omega⟩

/-- Appendix A, eq. (39) and Sec. 2.C: the closure operator `C = [-B_{N_t-1} | Id]`, written by
rows: `(C φ)_{kl} = φ_{1k} + φ_{kl} - φ_{1l}` for `1 < k < l`. -/
def closureOp (n : ℕ) : Matrix (ClosureIdx n) (Baseline n) ℝ :=
  fun c b =>
    (if b.1.1.1 = 0 ∧ b.1.2 = c.1.1 then 1 else 0) + (if b.1 = c.1 then 1 else 0) -
      (if b.1.1.1 = 0 ∧ b.1.2 = c.1.2 then 1 else 0)

/-- Sec. 3.B and Appendix B: the generalized inverse `C† = Cᵀ (C Cᵀ)⁻¹`. -/
def closurePinv (n : ℕ) : Matrix (Baseline n) (ClosureIdx n) ℝ :=
  (closureOp n)ᵀ * (closureOp n * (closureOp n)ᵀ)⁻¹

/-- Sec. 2.C, eq. (10): the three-telescope closure phase `β_{klm} = φ_{kl} + φ_{lm} + φ_{mk}` of
a family of phases `φ_{kl}` indexed by ordered pairs of telescopes. -/
def closurePhase {n : ℕ} (φ : Fin n → Fin n → ℝ) (k l m : Fin n) : ℝ :=
  φ k l + φ l m + φ m k

/-- Sec. 2.C: the canonical closure phases `β_{1kl}`, `1 < k < l`, grouped in a vector. -/
def canonicalClosure {n : ℕ} (φ : Fin n → Fin n → ℝ) (c : ClosureIdx n) : ℝ :=
  closurePhase φ ⟨0, lt_of_le_of_lt (Nat.zero_le _) c.1.1.2⟩ c.1.1 c.1.2

/-- Sec. 2.A: the vector `(φ_{kl})_{k<l}` of the baseline phases. -/
def baselineVec {n : ℕ} (φ : Fin n → Fin n → ℝ) : Baseline n → ℝ :=
  fun b => φ b.1.1 b.1.2

/-- Sec. 2.A, eq. (5): the object visibility phases `φ(x,t) = arg(H(t) x)` for the discretized
object `x` (real coefficients) and the discrete-continuous Fourier matrix `H(t)`. -/
def objPhase {n : ℕ} {P : Type*} [Fintype P] (H : Matrix (Baseline n) P ℂ) (x : P → ℝ) :
    Baseline n → ℝ :=
  fun b => Complex.arg ((H *ᵥ fun p => (x p : ℂ)) b)

/-- Sec. 3.B, eq. (24): the pseudo visibility phase data `φ^data(t) = C† β^data(t)`. -/
def pseudoPhase (n : ℕ) (βdata : ClosureIdx n → ℝ) : Baseline n → ℝ :=
  closurePinv n *ᵥ βdata

/-- Sec. 3.B, eq. (25): `φ^ker(t) = (C† C - Id) φ(x,t) + 2π C† κ`, for the integer vector `κ`
produced by the `2π` wrapping of the closure phases. -/
def kerPhase (n : ℕ) (φ : Baseline n → ℝ) (κ : ClosureIdx n → ℤ) : Baseline n → ℝ :=
  (closurePinv n * closureOp n - 1) *ᵥ φ + closurePinv n *ᵥ (fun c => 2 * Real.pi * κ c)

/-- Sec. 3.C, eq. (34): the myopic model `y_m(x, α(t)) = H(t) x · exp(i B̄ α(t))`
(componentwise product), with `α(t) ∈ ℝ^{N_t-1}` the phase aberrations. -/
def myopicModel {n : ℕ} {P : Type*} [Fintype P] (H : Matrix (Baseline n) P ℂ) (x : P → ℝ)
    (α : Fin (n - 1) → ℝ) : Baseline n → ℂ :=
  fun b => (H *ᵥ fun p => (x p : ℂ)) b *
    Complex.exp (Complex.I * ((baselineOpBar n *ᵥ α) b : ℂ))

/-- Sec. 3.C, display before eq. (35): the χ² statistic over the real and imaginary parts of
`y^data(t) - y_m - ȳ^noise(t)`, weighted by `R_{y^noise(t)}⁻¹`; the stacked real vector is
`[Re r; Im r]`, indexed by `Baseline n ⊕ Baseline n`. -/
def chi2 {n : ℕ} (ydata ybar : Baseline n → ℂ)
    (R : Matrix (Baseline n ⊕ Baseline n) (Baseline n ⊕ Baseline n) ℝ) (ym : Baseline n → ℂ) :
    ℝ :=
  let r : Baseline n → ℂ := ydata - ym - ybar
  let v : Baseline n ⊕ Baseline n → ℝ := Sum.elim (fun b => (r b).re) (fun b => (r b).im)
  v ⬝ᵥ (R⁻¹ *ᵥ v)

/-- Sec. 3.C, eq. (35): the myopic goodness-of-fit criterion
`J^data(x, α) = ∑_t χ²_{y(t)}(x, α(t))` over the finite set `T` of measurement instants, for the
pseudo complex visibilities `y^data(t)`, noise means `ȳ^noise(t)` and noise covariances
`R_{y^noise(t)}`. -/
def myopicCrit {n : ℕ} {T P : Type*} [Fintype T] [Fintype P]
    (H : T → Matrix (Baseline n) P ℂ) (ydata ybar : T → Baseline n → ℂ)
    (R : T → Matrix (Baseline n ⊕ Baseline n) (Baseline n ⊕ Baseline n) ℝ)
    (x : P → ℝ) (α : T → Fin (n - 1) → ℝ) : ℝ :=
  ∑ t, chi2 (ydata t) (ybar t) (R t) (myopicModel (H t) x (α t))

/-- Appendix E.A, eqs. (52)-(54): for polar data `a^data = ā + a^noise`, `φ^data = φ̄ + φ^noise`,
the complex noise `y^noise = a^data e^{i φ^data} - ā e^{i φ̄}` (componentwise). -/
def polarNoise {ι : Type*} (abar phibar anoise phinoise : ι → ℝ) (i : ι) : ℂ :=
  ((abar i + anoise i : ℝ) : ℂ) * Complex.exp (Complex.I * ((phibar i + phinoise i : ℝ) : ℂ)) -
    (abar i : ℂ) * Complex.exp (Complex.I * (phibar i : ℂ))

/-- Appendix E.A, eq. (54): the radial component `y^n_rad = Re(y^noise e^{-i φ̄})`. -/
def radNoise {ι : Type*} (abar phibar anoise phinoise : ι → ℝ) (i : ι) : ℝ :=
  (polarNoise abar phibar anoise phinoise i * Complex.exp (-(Complex.I * (phibar i : ℂ)))).re

/-- Appendix E.A, eq. (54): the tangential component `y^n_tan = Im(y^noise e^{-i φ̄})`. -/
def tanNoise {ι : Type*} (abar phibar anoise phinoise : ι → ℝ) (i : ι) : ℝ :=
  (polarNoise abar phibar anoise phinoise i * Complex.exp (-(Complex.I * (phibar i : ℂ)))).im

end Arxiv0812_1178


