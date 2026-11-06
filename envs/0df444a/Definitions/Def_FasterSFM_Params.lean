-- Prove2me | Definitions.Def_FasterSFM_Params
-- name    : FasterSFM_Params
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T01:33:48.26617+00:00
-- url     : https://prove2.me/theorems/2b04c16a-ce5e-4aa8-acdd-94afe808a647
-- title:
--   The constants $\lambda,\gamma,\tau,K$ and the size parameters $\delta,k_n,Q_n,\chi_n,M^*,W^*,B^*,\kappa^*$
-- statement:
--   The analysis of the algorithm fixes four universal constants
--
--   $$\lambda=2^{-10},\qquad \gamma=2^{-28},\qquad \tau=\frac{\lambda\sqrt\gamma}{16}=2^{-28},\qquad K=2^{100},$$
--
--   and, for a ground set of size $n$, the size parameters of eq. (10):
--
--   $$p_n=n+1,\quad \delta=(Kp_n)^{-20},\quad k_n=\frac{8n}{\gamma}\log\frac{1+2/\gamma}{\delta^2},\quad Q_n=k_n+n,\quad \chi_n=Q_n\delta .$$
--
--   Here $\delta$ is both the smallest offset of a cutting plane and the threshold separating wide steps from thin events, $k_n$ bounds the number of inserted rows and $Q_n$ the number of separation-oracle calls. The potential budget (15) uses $M^*=2n+k_n$, $W^*=n+\lambda M^*$ and $B^*=\tfrac n2\log(M^*/\delta^2)-\tfrac n2\log 2$; the accuracy bound (18) uses $e_n=2\sqrt n\,Q_n\delta$.
--
--   The recentering algorithm (Algorithm 1, line 3) uses $c=400/\lambda$, $\bar\tau=\tau/8$, $\tilde\tau=\tau/(32(3+\lambda))$, the initial parameter $\kappa_0=\log(\tau/(8n))$ and $\vartheta_0=1/(64\sqrt c)$; Lemma 18 sets $\varepsilon=\bar\tau^2/\lambda$, and p.35 defines
--
--   $$\kappa^*=\max\Big\{\kappa_0,\ \log\frac{8M^*W^{*2}(B^*+\varepsilon)}{\lambda^2\delta^2\tilde\tau^2}\Big\}.$$
--
--   These constants are shared by every geometric statement of the mission.
--
--   **Formalization Note** All quantities are real numbers and $\log$ is the natural logarithm. The PDF's text layer drops the bars on $\bar\tau$ and $\tilde\tau$; the values above are read from the rendered page 30.
-- source:
--   Ene & Nguyen, A Faster Strongly Polynomial Time Algorithm for Submodular Function Minimization, arXiv:2610.25403v1, §5.2, eq. (10), pp.17–18; eq. (15), p.26; eq. (18), p.28; Algorithm 1 line 3, p.30; Lemma 18, p.32; p.35

import Mathlib

namespace FasterSFM

/-!
# The fixed constants and the size parameters

Ene & Nguyen, arXiv:2610.25403v1, §5.2, eq. (10), pp.17–18; eq. (15), p.26; §6, eq. (18), p.28;
Algorithm 1 line 3, p.30; Lemma 18, p.32; p.35 (`τ̃`, `κ*`).

**Formalization Note.** All quantities are real numbers. `n` is the size of the original ground set
(the full-space dimension). `log` is the natural logarithm. The text layer of the PDF drops the bars:
`τ̄ = τ/8` and `τ̃ = τ/(32(3+λ))` (Algorithm 1, line 3, p.30, unbarred `τ` inside `τ̃`), and
`ε = τ̄²/λ` (Lemma 18, p.32).
-/

/-- `λ = 2⁻¹⁰`, the weight of the logarithmic barrier (§5.2, p.17). -/
noncomputable def lam : ℝ := 1 / 2 ^ 10

/-- `γ = 2⁻²⁸`, the leverage parameter of a new row (§5.2, p.17). -/
noncomputable def gam : ℝ := 1 / 2 ^ 28

/-- `τ = λ√γ/16 = 2⁻²⁸`, the tolerance of a certified center (12) (§5.2, p.17). -/
noncomputable def tau : ℝ := lam * Real.sqrt gam / 16

/-- `K = 2¹⁰⁰` (§5.2, p.17). -/
noncomputable def Kc : ℝ := 2 ^ 100

/-- `p_n = n + 1` (eq. (10), p.18). -/
noncomputable def pn (n : ℕ) : ℝ := (n : ℝ) + 1

/-- `δ = (K p_n)⁻²⁰`, the smallest offset and the wide/thin threshold (eq. (10), p.18). -/
noncomputable def delta (n : ℕ) : ℝ := ((Kc * pn n) ^ 20)⁻¹

/-- `k_n = (8n/γ) log((1 + 2/γ)/δ²)`, the bound on the number of inserted rows (eq. (10), p.18). -/
noncomputable def kn (n : ℕ) : ℝ := 8 * (n : ℝ) / gam * Real.log ((1 + 2 / gam) / delta n ^ 2)

/-- `Q_n = k_n + n`, the bound on separation-oracle calls (eq. (10), p.18). -/
noncomputable def Qn (n : ℕ) : ℝ := kn n + n

/-- `χ_n = Q_n δ`, the width bound at a thin event (eq. (10), p.18). -/
noncomputable def chi (n : ℕ) : ℝ := Qn n * delta n

/-- `M* = 2n + k_n` (eq. (14), p.25 and eq. (15), p.26). -/
noncomputable def Mstar (n : ℕ) : ℝ := 2 * (n : ℝ) + kn n

/-- `W* = n + λ M*` (eq. (15), p.26). -/
noncomputable def Wstar (n : ℕ) : ℝ := (n : ℝ) + lam * Mstar n

/-- `B* = (n/2) log(M*/δ²) − (n/2) log 2`, the potential budget (eq. (15), p.26). -/
noncomputable def Bstar (n : ℕ) : ℝ :=
  (n : ℝ) / 2 * Real.log (Mstar n / delta n ^ 2) - (n : ℝ) / 2 * Real.log 2

/-- `e_n = 2√n Q_n δ`, the accuracy bound (18) (p.28). -/
noncomputable def en (n : ℕ) : ℝ := 2 * Real.sqrt n * Qn n * delta n

/-- `c = 400/λ`, the self-concordance scaling (Lemma 9, p.19; Algorithm 1, line 3). -/
noncomputable def cSC : ℝ := 400 / lam

/-- `τ̄ = τ/8`, the tolerance of the phase test (Algorithm 1, line 3, p.30). -/
noncomputable def taubar : ℝ := tau / 8

/-- `τ̃ = τ/(32(3+λ))`, the tolerance of the projection test (Algorithm 1, line 3, p.30;
p.35). -/
noncomputable def tautilde : ℝ := tau / (32 * (3 + lam))

/-- `κ₀ = log(τ/(8n))`, the initial penalty parameter (Algorithm 1, line 3, p.30). -/
noncomputable def kappa0 (n : ℕ) : ℝ := Real.log (tau / (8 * (n : ℝ)))

/-- `ϑ₀ = 1/(64√c)` (Algorithm 1, line 3, p.30). -/
noncomputable def theta0 : ℝ := 1 / (64 * Real.sqrt cSC)

/-- `ε = τ̄²/λ` (Lemma 18, p.32). -/
noncomputable def eps : ℝ := taubar ^ 2 / lam

/-- `κ* = max{κ₀, log(8 M* W*² (B* + ε)/(λ² δ² τ̃²))}` (p.35). -/
noncomputable def kappaStar (n : ℕ) : ℝ :=
  max (kappa0 n)
    (Real.log (8 * Mstar n * Wstar n ^ 2 * (Bstar n + eps) / (lam ^ 2 * delta n ^ 2 * tautilde ^ 2)))

end FasterSFM


