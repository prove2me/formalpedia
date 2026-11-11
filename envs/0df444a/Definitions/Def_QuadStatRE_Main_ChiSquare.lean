-- Prove2me | Definitions.Def_QuadStatRE_Main_ChiSquare
-- name    : QuadStatRE_Main_ChiSquare
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T22:47:02.621907+00:00
-- url     : https://prove2.me/theorems/b59aa6b4-f946-405b-8264-dcab4bfc785a
-- title:
--   $\chi^2$-distance, normalized $\chi^2$-information $\tau$, Gram matrix $K_{W,R}$, $\Lambda_R$, the counting polynomial $P$, the code $D$ and the RM bound $B$
-- statement:
--   For distributions $P,Q$ on a finite set, the **$\chi^2$-distance** (p. 12) is
--   $$\chi^2(P\|Q)=\sum_{\omega:\,Q(\omega)>0}\frac{(P(\omega)-Q(\omega))^2}{Q(\omega)},$$
--   used when $\operatorname{supp}P\subseteq\operatorname{supp}Q$. For a leakage family $W$ with mixture $M$, the **normalized $\chi^2$-information** (p. 28) is
--   $$\tau(W)=\frac{I_{\chi^2}(S;T)}{7}=\frac1{56}\sum_{s\in G}\chi^2(W_s\|M).$$
--   For a reference distribution $R$, the **likelihood Gram matrix** (6.5) is $K_{W,R}(s,t)=\mathbb E_{T\leftarrow R}\big[\tfrac{W_s(T)}{R(T)}\tfrac{W_t(T)}{R(T)}\big]$ and the **average likelihood second moment** is $\Lambda_R(W)=\frac18\sum_sK_{W,R}(s,s)$ (p. 30).
--
--   For $A\in\mathbb F_2^{3\times4}$ let $w(A)=|\{u\in I:Au\ne0\}|$. The **counting polynomial** (6.2) is
--   $$P(z)=\mathbb E_{A\leftarrow\mathbb F_2^{3\times4}}\big[(1+7z)^{15-w(A)}(1-z)^{w(A)}\big].$$
--   The **code** $D$ of Remark 6.3 is $\{\delta\in G^I:\sum_{u\in I}u_i\delta_u=0\text{ for every }i\in[4]\}$, with Hamming weight $\mathrm{wt}(\delta)=|\{u:\delta_u\ne0\}|$ and weight enumerator $\sum_{\delta\in D}z^{\mathrm{wt}(\delta)}$. The **RM bound** (6.8) is $B(\theta)=(\sqrt{P(\theta)}-1)/(\sqrt8-1)$, $\theta\ge0$.
--
--   $\tau$ is the single number through which the paper measures leakage; $P$ and $B$ describe exactly how one RM step transforms it.
--
--   **Formalization Note.** $P$ and the weight enumerator are polynomials in $\mathbb R[z]$. The expectation under $R$ in $K_{W,R}$ is $\sum_\omega R(\omega)\cdot(\dots)$, so terms with $R(\omega)=0$ contribute nothing. $B$ is defined for every real $\theta$ and used only at $\theta=\tau(W)\ge0$. $I$ is indexed as in the RM sharing definition.
-- source:
--   Applebaum, Quadratic Statistical Randomized Encoding for All Functions, STOC 2027 submission (manuscript sha256 000cbf4e…), p. 12 (χ²), p. 28 (τ), pp. 29–31 ((6.2), Remark 6.3, (6.5), Λ_R, (6.8))

import Mathlib
import Definitions.Def_QuadStatRE_Main_LeakageFamily
import Definitions.Def_QuadStatRE_Main_RMSharing

namespace QuadStatRE.Main

open QuadraticRE Polynomial

/-- The `χ²`-distance (Applebaum, *Quadratic Statistical Randomized Encoding for All Functions*,
STOC 2027 submission, §2.1, p. 12): `χ²(P ∥ Q) = ∑_{ω : Q(ω) > 0} (P(ω) − Q(ω))² / Q(ω)`, used when
`supp(P) ⊆ supp(Q)`. -/
noncomputable def chiSq {Ω : Type} [Fintype Ω] (P Q : Ω → ℝ) : ℝ :=
  ∑ ω ∈ Finset.univ.filter (fun ω => 0 < Q ω), (P ω - Q ω) ^ 2 / Q ω

/-- The normalized `χ²`-information (§6.1, p. 28):
`τ(W) = I_{χ²}(S; T) / 7 = (1/56) ∑_{s ∈ G} χ²(W_s ∥ M)`, with `M` the uniform mixture. -/
noncomputable def tau {Ω : Type} [Fintype Ω] (W : G → Ω → ℝ) : ℝ :=
  (1 / 56 : ℝ) * ∑ s : G, chiSq (W s) (mix W)

/-- The likelihood Gram matrix (6.5), p. 30:
`K_{W,R}(s, t) = E_{T ← R}[(W_s(T)/R(T)) (W_t(T)/R(T))]`, the expectation under `R` written as
`∑_ω R(ω) · (…)` (terms with `R(ω) = 0` vanish). -/
noncomputable def gram {Ω : Type} [Fintype Ω] (W : G → Ω → ℝ) (R : Ω → ℝ) (s t : G) : ℝ :=
  ∑ ω, R ω * ((W s ω / R ω) * (W t ω / R ω))

/-- The average likelihood second moment, p. 30: `Λ_R(W) = (1/8) ∑_{s ∈ G} K_{W,R}(s, s)`. -/
noncomputable def Lam {Ω : Type} [Fintype Ω] (R : Ω → ℝ) (W : G → Ω → ℝ) : ℝ :=
  (1 / 8 : ℝ) * ∑ s : G, gram W R s s

/-- `w(A) = |{u ∈ I : A u ≠ 0}|` (§6.2, p. 29). -/
def wA (A : Matrix (Fin 3) (Fin 4) F2) : ℕ :=
  (Finset.univ.filter (fun k : Fin 15 => A.mulVec (uvec k) ≠ 0)).card

/-- The counting polynomial (6.2), p. 29:
`P(z) = E_{A ← F₂^{3×4}}[(1 + 7z)^{15 − w(A)} (1 − z)^{w(A)}]`, as a real polynomial. -/
noncomputable def countPoly : ℝ[X] :=
  ∑ A : Matrix (Fin 3) (Fin 4) F2,
    C (1 / 4096 : ℝ) * (1 + C 7 * X) ^ (15 - wA A) * (1 - X) ^ (wA A)

/-- The code `D` of Remark 6.3, p. 29: words `δ ∈ G^I` with `∑_{u ∈ I} u_i δ_u = 0` for every
`i ∈ [4]`. -/
def codeD : Finset (Fin 15 → G) :=
  Finset.univ.filter (fun δ => ∀ i : Fin 4, ∑ k : Fin 15, uvec k i • δ k = 0)

/-- The Hamming weight of a word of `G^I`: the number of positions with `δ_u ≠ 0`. -/
def hammingWt (δ : Fin 15 → G) : ℕ :=
  (Finset.univ.filter (fun k : Fin 15 => δ k ≠ 0)).card

/-- The Hamming weight enumerator of `D`: `∑_{δ ∈ D} z^{wt(δ)}`. -/
noncomputable def weightEnumD : ℝ[X] :=
  ∑ δ ∈ codeD, X ^ (hammingWt δ)

/-- The RM bound (6.8), p. 31: `B(θ) = (√P(θ) − 1)/(√8 − 1)`, `θ ≥ 0`.

**Formalization Note.** Defined for every real `θ`; it is used only at `θ = τ(W) ≥ 0`. -/
noncomputable def B (θ : ℝ) : ℝ :=
  (Real.sqrt (countPoly.eval θ) - 1) / (Real.sqrt 8 - 1)

end QuadStatRE.Main


