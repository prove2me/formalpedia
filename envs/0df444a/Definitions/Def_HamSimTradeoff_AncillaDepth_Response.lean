-- Prove2me | Definitions.Def_HamSimTradeoff_AncillaDepth_Response
-- name    : HamSimTradeoff_AncillaDepth_Response
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-10T20:45:24.698687+00:00
-- url     : https://prove2.me/theorems/c6714455-fe70-4177-abf7-9c65ff8d1df8
-- title:
--   Hard family, recursive response coefficients, and controller moments
-- statement:
--   Let $X=\left(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\right)$ and $Z=\left(\begin{smallmatrix}1&0\\0&-1\end{smallmatrix}\right)$ be the Pauli matrices. For every $L\ge2$ and all positive weights with $\alpha_1=1/2$ and $\sum_j\alpha_j=1$, set
--   $$H_1(\delta)=-(\cos\delta)Z+(\sin\delta)X,\quad H_j(\delta)=Z\ (j\ge2),\quad A(\delta)=\tfrac12\sin\delta\,X+\tfrac12(1-\cos\delta)Z.$$
--   For real $h$, define $\rho_1(h)=\sin(h/2)/h$ with $\rho_1(0)=1/2$, and recursively
--   $$\rho_k(h)=4u_k\rho_{k-1}(u_kh)+(1-4u_k)\rho_{k-1}((1-4u_k)h).$$
--   Define $c_{1,n}=(-1)^n/[2^{2n+1}(2n+1)!]$ and $c_{k,n}=c_{k-1,n}[4u_k^{2n+1}+(1-4u_k)^{2n+1}]$. For the architecture, let $|a_\ell\rangle=V_{\ell-1}\cdots V_0|0^a\rangle$, $\langle b_\ell|=\langle0^a|V_s\cdots V_\ell$, and
--   $$\omega_{\ell r}=\langle b_\ell|r\rangle\langle r|a_\ell\rangle,\qquad M_n=\frac1s\sum_{\ell,r}\omega_{\ell r}m_{\ell r}^{-2n},$$
--   $$g(t)=-it\left(\frac1s\sum_{\ell,r}\omega_{\ell r}\rho_k\!\left(\frac{t}{sm_{\ell r}}\right)-\frac\eta2\right).$$
--   These explicit recursions and finite sums define the witnesses in the lower-bound argument. No derivative identity, small-error estimate, or nonvanishing conclusion is assumed by their definitions; those are separate theorem targets.
--
--   **Formalization Note** The weights range over all source choices rather than just the two-term reduction. Prefixes and suffixes are ordinary ordered products without inserting adjoints. The auxiliary level convention agrees with the Suzuki definition.
-- source:
--   Yuxin Zhang, Changpeng Shao, Time-space tradeoffs for Hamiltonian simulation, STOC 2027 submission #334 (October 2026), pp.14–16, Eq. (3.1), Lemma 3.1, Eqs. (3.3)–(3.4), and unnumbered response displays

import Definitions.Def_HamSimTradeoff_AncillaDepth_Architecture
open scoped BigOperators Matrix.Norms.L2Operator

namespace HamSimTradeoff.AncillaDepth
noncomputable section

def pauliX : Mat 2 := !![0, 1; 1, 0]
def pauliZ : Mat 2 := !![1, 0; 0, -1]

def hardH (L : ℕ) (delta : ℝ) (j : Fin L) : Mat 2 :=
  if j.val = 0 then (-Real.cos delta : ℂ) • pauliZ + (Real.sin delta : ℂ) • pauliX else pauliZ

/-- Every choice of positive weights allowed in (3.1), including arbitrary L ≥ 2. -/
structure HardWeights (L : ℕ) where
  two_le : 2 ≤ L
  alpha : Fin L → ℝ
  pos : ∀ j, 0 < alpha j
  sum_eq : ∑ j, alpha j = 1
  first : alpha ⟨0, by omega⟩ = 1 / 2

def hardA (delta : ℝ) : Mat 2 :=
  (Real.sin delta / 2 : ℂ) • pauliX + ((1 - Real.cos delta) / 2 : ℂ) • pauliZ

def hardCompression {L : ℕ} (B : Architecture) (w : HardWeights L) (t delta : ℝ) : Mat 2 :=
  compression B w.alpha (hardH L delta) t

/-- The quotient has its continuous value 1/2 at zero, rather than Lean's 0/0 value. -/
def rhoLevel : ℕ → ℝ → ℝ
  | 0, h => if h = 0 then 1 / 2 else Real.sin (h / 2) / h
  | q + 1, h => 4 * u (q + 2) * rhoLevel q (u (q + 2) * h) +
      (1 - 4 * u (q + 2)) * rhoLevel q ((1 - 4 * u (q + 2)) * h)

def rho (k : ℕ) (h : ℝ) : ℝ := rhoLevel (k - 1) h

def coefficientLevel : ℕ → ℕ → ℝ
  | 0, n => (-1 : ℝ) ^ n / (2 ^ (2 * n + 1) * (Nat.factorial (2 * n + 1) : ℝ))
  | q + 1, n => coefficientLevel q n *
      (4 * u (q + 2) ^ (2 * n + 1) + (1 - 4 * u (q + 2)) ^ (2 * n + 1))

def coefficient (k n : ℕ) : ℝ := coefficientLevel (k - 1) n

/-- ell=0 represents paper round 1; the prefix is V_ell ... V_0. -/
def controllerPrefix (B : Architecture) (ell : Fin B.s) : Mat (2 ^ B.a) :=
  (((List.finRange (B.s + 1)).filter (fun j => j.val ≤ ell.val)).reverse.map (controller B)).prod

/-- The suffix is V_s ... V_(ell+1), without adjoints. -/
def suffix (B : Architecture) (ell : Fin B.s) : Mat (2 ^ B.a) :=
  (((List.finRange (B.s + 1)).filter (fun j => ell.val < j.val)).reverse.map (controller B)).prod

def omega (B : Architecture) (ell : Fin B.s) (r : Fin (2 ^ B.a)) : ℂ :=
  suffix B ell (ancillaZero B.a) r * controllerPrefix B ell r (ancillaZero B.a)

def moment (B : Architecture) (n : ℕ) : ℂ :=
  (B.s : ℂ)⁻¹ * ∑ ell, ∑ r, omega B ell r / (B.m ell r : ℂ) ^ (2 * n)

/-- Explicit finite formula, subsequently linked to the derivative and the Taylor series. -/
def response (B : Architecture) (t : ℝ) : ℂ :=
  -Complex.I * (t : ℂ) *
    ((B.s : ℂ)⁻¹ * ∑ ell, ∑ r,
      omega B ell r * (rho B.k (t / ((B.s : ℝ) * B.m ell r)) : ℂ) - eta B / 2)

end
end HamSimTradeoff.AncillaDepth


