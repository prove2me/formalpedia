-- Prove2me | Definitions.Def_LeeCutCertificates_Certificate_Supplement_Budgets
-- name    : LeeCutCertificates_Certificate_Supplement_Budgets
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T19:03:39.779109+00:00
-- url     : https://prove2.me/theorems/b6964d5b-5862-4a67-bcc6-18eef2bdc936
-- title:
--   Public integer logs and exact oracle budgets
-- statement:
--   Set $L(n)=\max\{1,\lceil\log_2(2n)\rceil\}$, $K(n)=L(L(n))$, $a(n)=268L(n)K(n)$, $\rho_0=42$ and $\gamma(n)=(100a(n)^2\rho_0^2)^{-1}$. For $M$ nonroot clusters define
--
--   $$Q(n,M,q)=M\bigl(1+4(q-1)(\lfloor\log_2n\rfloor+3)\bigr).$$
--
--   The direct budget uses $q=\lceil200\rho_0^2B^2\rceil$; a refinement uses $q=\lceil2B/\gamma\rceil$ and adds $2n$ new-cluster queries. A public upper envelope for all refinement rounds and the final direct completion is
--
--   $$400000\cdot268^2\cdot42^4\,(M+2n)B L(n)^3K(n)^2.$$
--
--   Conversion first normalizes offline and adds at most $2n$ initial queries to this envelope with $M=2n$. The real learning threshold is $3433597776\,\ln^2(2n)(\ln\ln(2n))^2$. These are numeric functions of public data, without an assumed algorithmic guarantee.
--
--   **Formalization Note** Appendix A supplies the primitive caps; §10.3's geometric sum gives the envelope (derived in MODERATION_NOTES.md). The natural-log threshold is $2\cdot3892968\cdot9\cdot49$. Values at $n=0$ are total conventions; the graph theorems require $n\ge2$.
-- source:
--   Troy Lee, Finding and Certifying Weighted Minimum Cuts with Cut Queries, STOC 2027 submission #474 (October 2026), §10.1–10.4, printed pp.30–33 (PDF pp.31–34); §11.7–11.8, printed pp.40–42 (PDF pp.41–43); Appendix A, printed pp.53–56 (PDF pp.54–57)

import Definitions.Def_LeeCutCertificates_Certificate_CutQueries

set_option autoImplicit false

namespace LeeCutCertificates.Certificate.Supplement

/-- Appendix A integer logs, also total at n = 0. -/
def logL (n : ℕ) : ℕ := max 1 (ceilLog2 (2 * n))
def logK (n : ℕ) : ℕ := logL (logL n)
def offlineFactor (n : ℕ) : ℝ := 268 * logL n * logK n
def guardQuality : ℝ := 42
noncomputable def gamma (n : ℕ) : ℝ := 1 / (100 * offlineFactor n ^ 2 * guardQuality ^ 2)

/-- M is the number of nonroot nodes, counting repeated and empty clusters. -/
noncomputable def completionCap (n M : ℕ) (q : ℕ) : ℕ :=
  M * (1 + 4 * (q - 1) * (Nat.log 2 n + 3))

noncomputable def suppliedCap (n M : ℕ) (B : ℝ) : ℕ :=
  completionCap n M ⌈200 * guardQuality ^ 2 * B ^ 2⌉₊

/-- A refinement includes its old capacity queries and at most 2n new ones. -/
noncomputable def roundCap (n M : ℕ) (B : ℝ) : ℕ :=
  completionCap n M ⌈2 * B / gamma n⌉₊ + 2 * n

/-- A public envelope for the geometric refinement sum, including initial cluster queries.
Its coefficient retains the initial size M; no depth or log B factor is charged. -/
def refinementCap (n M : ℕ) (B : ℝ) : ℝ :=
  400000 * (268 : ℝ)^2 * (42 : ℝ)^4 * (M + 2 * n) * B * logL n ^ 3 * logK n ^ 2

/-- Conversion normalizes the arbitrary input tree to at most 2n nonroot clusters offline. -/
def conversionCap (n : ℕ) (B : ℝ) : ℝ :=
  2 * n + refinementCap n (2 * n) B

/-- The exact real-parameter lower threshold from Theorem 7, in natural logarithms. -/
noncomputable def learningThreshold (n : ℕ) : ℝ :=
  3433597776 * Real.log (2 * (n : ℝ)) ^ 2 * Real.log (Real.log (2 * (n : ℝ))) ^ 2

end LeeCutCertificates.Certificate.Supplement


