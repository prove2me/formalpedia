-- Prove2me | Definitions.Def_NoonAmp_Symmetric_Model
-- name    : NoonAmp_Symmetric_Model
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-22T02:22:55.896905+00:00
-- url     : https://prove2.me/theorems/c8f2f387-a027-48f0-b335-1fa07b78a93e
-- title:
--   (1), (5), (11), (12), (14), (17), pp. 1–3 — NOON density, symmetric two-mode quantum-limited amplifier, two-mode Q function, ρG, photon-added and number-basis output matrices
-- statement:
--   This module fixes the objects of §II of Agarwal, Chaturvedi and Rai, *Amplification of NOON States*, on the two-mode Fock space $\ell^2(\mathbb N\times\mathbb N)$ with orthonormal number basis $|n,m\rangle$ ($n$ photons in mode $a$, $m$ photons in mode $b$). An operator $X$ is described by its matrix $\langle p|X|q\rangle$, $p,q\in\mathbb N\times\mathbb N$.
--
--   1. **Matrix realization.** $X$ *has matrix* $K$ if $\langle p|X|q\rangle = K(p,q)$ for all $p,q$. The operator built from a matrix $K$ is the unique bounded operator with matrix $K$ when one exists, and $0$ otherwise; every theorem that uses such an operator proves that it exists.
--   2. **NOON state (1), (11).** For an integer $N$, $|\mathrm{NOON}\rangle = \tfrac{1}{\sqrt2}\big(|N,0\rangle + |0,N\rangle\big)$ and $\rho_{\mathrm{in}} = |\mathrm{NOON}\rangle\langle \mathrm{NOON}|$; the vacuum is $\rho_0 = |0,0\rangle\langle 0,0|$.
--   3. **Symmetric quantum-limited amplifier.** For amplitude gain $G$ the single-mode Kraus operators $A_\ell(G)$, $\ell\in\mathbb N$, are the weighted raising shifts
--   $$\langle n+\ell|A_\ell(G)|n\rangle = \frac1G\sqrt{\binom{n+\ell}{\ell}}\Big(1-\frac1{G^2}\Big)^{\ell/2} G^{-n},$$
--   all other entries $0$ (the published module P39). The symmetric two-mode amplifier has Kraus operators $A_\ell(G)\otimes A_{\ell'}(G)$, $(\ell,\ell')\in\mathbb N^2$, and maps $\rho$ to the trace-norm convergent sum $\sum_{\ell,\ell'} (A_\ell\otimes A_{\ell'})\,\rho\,(A_\ell\otimes A_{\ell'})^\dagger$.
--   4. **Two-mode Q function (5), (12).** With the two-mode coherent state $|\alpha,\beta\rangle = |\alpha\rangle\otimes|\beta\rangle$, $\langle n|\alpha\rangle = e^{-|\alpha|^2/2}\alpha^n/\sqrt{n!}$,
--   $$Q_X(\alpha,\beta) = \frac{1}{\pi^2}\,\mathrm{Re}\,\langle \alpha,\beta|X|\alpha,\beta\rangle .$$
--   5. **Amplified vacuum (14).** $\beta_G = \ln\!\big(G^2/(G^2-1)\big)$ and $\rho_G = G^{-4}e^{-\beta_G(a^\dagger a + b^\dagger b)}$, the diagonal matrix with entries $G^{-4}e^{-\beta_G(n+m)}$ at $|n,m\rangle$.
--   6. **Creation and annihilation operators on matrices.** For a matrix $K$, $a^{\dagger N}K$ and $K a^{N}$ are the matrices
--   $$\langle (r,s)|a^{\dagger N}K|q\rangle = \sqrt{\tfrac{r!}{(r-N)!}}\,K\big((r-N,s),q\big)\ (r\ge N),\qquad \langle p|K a^N|(r,s)\rangle = K\big(p,(r-N,s)\big)\sqrt{\tfrac{r!}{(r-N)!}}\ (r\ge N),$$
--   and $0$ otherwise; likewise for mode $b$ on the second index.
--   7. **Photon-added form (14).** The matrix $\frac{1}{2N!G^{2N}}\big[a^{\dagger N}\rho_G a^N + a^{\dagger N}\rho_G b^N + b^{\dagger N}\rho_G a^N + b^{\dagger N}\rho_G b^N\big]$.
--   8. **Number-basis output (17).** The matrix whose $(p,q)$ entry is the double series $\sum_{n,m\ge0}$ of the $(p,q)$ entries of
--   $$\frac{1}{2N!G^{2N+4}}\Big(\frac{G^2-1}{G^2}\Big)^{n+m}\Big[\tfrac{(n+N)!}{n!}|n+N,m\rangle\langle n+N,m| + \tfrac{(m+N)!}{m!}|n,m+N\rangle\langle n,m+N| + \sqrt{\tfrac{(n+N)!}{n!}\tfrac{(m+N)!}{m!}}\big(|n+N,m\rangle\langle n,m+N| + |n,m+N\rangle\langle n+N,m|\big)\Big].$$
--
--   These are the objects in which the paper's results (12)–(17) are stated; each is written exactly as on the page, with the constants $1/2$, $1/(2N!)$, $1/\pi^2$, $1/G^4$, $1/(2N!G^{2N})$, $1/(2N!G^{2N+4})$ in place.
--
--   **Formalization Note** The paper models the amplifier by the master equation (2) in the limit $\eta\to0$ and uses it only through its Q-function action (7), $Q_{\mathrm{out}}(\alpha) = G^{-2}Q_{\mathrm{in}}(\alpha/G)$. Here the amplifier is the standard quantum-limited amplifier in Kraus form; that its Q action is exactly (7) is the open platform theorem `Dependency50.P39.amplifierHusimiScaling`, which is why this Kraus family is the paper's channel. The two-mode objects reuse P39's `BipartiteFock`, `bipartiteKet` (mode $a$ first), `amplifierMatrix` and `coherentCoefficient`. Creation and annihilation operators are unbounded and are used only as the index shifts above. Operators defined from matrices or coefficient sequences fall back to $0$ when no bounded realization exists; the theorems conclude the realization.
-- source:
--   Agarwal, Chaturvedi, Rai, Amplification of NOON States, arXiv:0912.5134v1, pp. 1–3, (1), (5), (7), (11), (12), (14), (16), (17)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P39

noncomputable section

namespace NoonAmp.Symmetric

open QAlgorithms.Papers.Independent.Dependency50.P39

attribute [local instance] Classical.propDecidable

/-- `⟨p|A|q⟩ = K p q` on the two-mode number basis; `p = (mode a, mode b)`, so
`bipartiteKet (n, m)` is the paper's `|n, m⟩` (arXiv:0912.5134v1, p. 1). -/
def HasBipartiteMatrix (A : BipartiteOperator) (K : ℕ × ℕ → ℕ × ℕ → ℂ) : Prop :=
  ∀ p q, A (bipartiteKet q) p = K p q

/-- The unique bounded operator with matrix `K` when it exists, and `0` otherwise
(the pattern of P39 `operatorOfMatrix`). Every theorem using it concludes the
realization `HasBipartiteMatrix`, so the fallback is never used silently. -/
def bipartiteOperatorOfMatrix (K : ℕ × ℕ → ℕ × ℕ → ℂ) : BipartiteOperator :=
  if h : ∃ A : BipartiteOperator, HasBipartiteMatrix A K then Classical.choose h else 0

/-- (1), p. 1: number-basis coefficients of `|NOON⟩ = (1/√2)(|N, 0⟩ + |0, N⟩)`. -/
def noonCoeff (N : ℕ) (p : ℕ × ℕ) : ℂ :=
  (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * ((if p = (N, 0) then 1 else 0) + (if p = (0, N) then 1 else 0))

/-- (11), p. 2: the matrix of `ρin = |NOON⟩⟨NOON|`. -/
def noonMatrix (N : ℕ) (p q : ℕ × ℕ) : ℂ := noonCoeff N p * star (noonCoeff N q)

/-- (11), p. 2: the NOON density operator `ρin`. -/
def noonDensity (N : ℕ) : BipartiteOperator := bipartiteOperatorOfMatrix (noonMatrix N)

/-- The matrix of the dyad `|u⟩⟨v|` on the two-mode number basis. -/
def pairDyad (u v p q : ℕ × ℕ) : ℂ := if p = u ∧ q = v then 1 else 0

/-- (11), p. 2: the two-mode vacuum `ρ0 = |0, 0⟩⟨0, 0|`. -/
def vacuumPair : BipartiteOperator :=
  InnerProductSpace.rankOne ℂ (bipartiteKet (0, 0)) (bipartiteKet (0, 0))

/-- Symmetric amplification: the matrix of `A_ℓ(G) ⊗ A_ℓ'(G)`, `l = (ℓ, ℓ')`, where
`A_ℓ(G)` is the quantum-limited amplifier Kraus operator of P39 (`amplifierMatrix`,
amplitude gain `G`). -/
def symAmpMatrix (G : ℝ) (l : ℕ × ℕ) (p q : ℕ × ℕ) : ℂ :=
  amplifierMatrix G l.1 p.1 q.1 * amplifierMatrix G l.2 p.2 q.2

/-- The Kraus operator `A_ℓ(G) ⊗ A_ℓ'(G)` of the symmetric two-mode amplifier. -/
def symAmpKraus (G : ℝ) (l : ℕ × ℕ) : BipartiteOperator :=
  bipartiteOperatorOfMatrix (symAmpMatrix G l)

/-- Every symmetric Kraus operator is a bounded operator with the displayed matrix. -/
def SymAmpRealized (G : ℝ) : Prop :=
  ∀ l, HasBipartiteMatrix (symAmpKraus G l) (symAmpMatrix G l)

/-- One Kraus term `L X L†`; the channel output is the trace-norm sum over the
Kraus index (P39 `TraceHasSum`). -/
def bipartiteKrausTerm (A X : BipartiteOperator) : BipartiteOperator :=
  (A.comp X).comp (ContinuousLinearMap.adjoint A)

/-- Number-basis coefficients of the two-mode coherent state `|α, β⟩ = |α⟩ ⊗ |β⟩`. -/
def coherentPairCoefficient (α β : ℂ) (p : ℕ × ℕ) : ℂ :=
  coherentCoefficient α p.1 * coherentCoefficient β p.2

/-- The two-mode coherent vector `|α, β⟩` when square-summable, and `0` otherwise. -/
def coherentPairKet (α β : ℂ) : BipartiteFock :=
  if h : ∃ u : BipartiteFock, ∀ p, u p = coherentPairCoefficient α β p then
    Classical.choose h else 0

/-- Every two-mode coherent vector exists with the displayed coefficients and unit norm. -/
def CoherentPairRealized : Prop :=
  ∀ α β : ℂ, (∀ p, coherentPairKet α β p = coherentPairCoefficient α β p) ∧
    ‖coherentPairKet α β‖ = 1

/-- (5), (12), p. 2: the two-mode Q function `Q(α, β) = (1/π²) ⟨α, β|X|α, β⟩`,
with the paper's factor `1/π` per mode. -/
def husimiQ2 (X : BipartiteOperator) (α β : ℂ) : ℝ :=
  (Real.pi ^ 2)⁻¹ * (inner (𝕜 := ℂ) (coherentPairKet α β) (X (coherentPairKet α β))).re

/-- (14), p. 3: `β = ln(G²/(G² − 1))`. -/
def ampBeta (G : ℝ) : ℝ := Real.log (G ^ 2 / (G ^ 2 - 1))

/-- (14), p. 3: the matrix of `ρG = G⁻⁴ e^{−β(a†a + b†b)}`, diagonal in the number basis. -/
def rhoGMatrix (G : ℝ) (p q : ℕ × ℕ) : ℂ :=
  if p = q then (((G ^ 4)⁻¹ * Real.exp (-(ampBeta G) * ((p.1 + p.2 : ℕ) : ℝ)) : ℝ) : ℂ) else 0

/-- `√(r!/(r − N)!)`: `a†ᴺ|r − N⟩ = √(r!/(r − N)!) |r⟩` for `N ≤ r`. -/
def raiseCoeff (N r : ℕ) : ℂ :=
  ((Real.sqrt ((r.factorial : ℝ) / ((r - N).factorial : ℝ)) : ℝ) : ℂ)

/-- `⟨p|a†ᴺ K|q⟩`: left multiplication of the matrix `K` by `a†ᴺ` (mode a). -/
def raiseA (N : ℕ) (K : ℕ × ℕ → ℕ × ℕ → ℂ) (p q : ℕ × ℕ) : ℂ :=
  if N ≤ p.1 then raiseCoeff N p.1 * K (p.1 - N, p.2) q else 0

/-- `⟨p|b†ᴺ K|q⟩`: left multiplication of the matrix `K` by `b†ᴺ` (mode b). -/
def raiseB (N : ℕ) (K : ℕ × ℕ → ℕ × ℕ → ℂ) (p q : ℕ × ℕ) : ℂ :=
  if N ≤ p.2 then raiseCoeff N p.2 * K (p.1, p.2 - N) q else 0

/-- `⟨p|K aᴺ|q⟩`: right multiplication of the matrix `K` by `aᴺ = (a†ᴺ)†`. -/
def lowerA (N : ℕ) (K : ℕ × ℕ → ℕ × ℕ → ℂ) (p q : ℕ × ℕ) : ℂ :=
  if N ≤ q.1 then K p (q.1 - N, q.2) * raiseCoeff N q.1 else 0

/-- `⟨p|K bᴺ|q⟩`: right multiplication of the matrix `K` by `bᴺ = (b†ᴺ)†`. -/
def lowerB (N : ℕ) (K : ℕ × ℕ → ℕ × ℕ → ℂ) (p q : ℕ × ℕ) : ℂ :=
  if N ≤ q.2 then K p (q.1, q.2 - N) * raiseCoeff N q.2 else 0

/-- (14), p. 3: the matrix of
`(1/(2N!G²ᴺ)) [a†ᴺρGaᴺ + a†ᴺρGbᴺ + b†ᴺρGaᴺ + b†ᴺρGbᴺ]`. -/
def photonAddedMatrix (G : ℝ) (N : ℕ) (p q : ℕ × ℕ) : ℂ :=
  (((2 * (N.factorial : ℝ) * G ^ (2 * N))⁻¹ : ℝ) : ℂ) *
    (lowerA N (raiseA N (rhoGMatrix G)) p q + lowerB N (raiseA N (rhoGMatrix G)) p q +
      lowerA N (raiseB N (rhoGMatrix G)) p q + lowerB N (raiseB N (rhoGMatrix G)) p q)

/-- (17), p. 3: the `(n, m)` summand of the number-basis form of `ρout`, evaluated at
`⟨p|·|q⟩`; `nm = (n, m)`. -/
def noonOutputTerm (G : ℝ) (N : ℕ) (p q : ℕ × ℕ) (nm : ℕ × ℕ) : ℂ :=
  let fa : ℝ := ((nm.1 + N).factorial : ℝ) / (nm.1.factorial : ℝ)
  let fb : ℝ := ((nm.2 + N).factorial : ℝ) / (nm.2.factorial : ℝ)
  (((2 * (N.factorial : ℝ) * G ^ (2 * N + 4))⁻¹ * ((G ^ 2 - 1) / G ^ 2) ^ (nm.1 + nm.2) : ℝ) : ℂ) *
    ((fa : ℂ) * pairDyad (nm.1 + N, nm.2) (nm.1 + N, nm.2) p q +
      (fb : ℂ) * pairDyad (nm.1, nm.2 + N) (nm.1, nm.2 + N) p q +
      ((Real.sqrt (fa * fb) : ℝ) : ℂ) *
        (pairDyad (nm.1 + N, nm.2) (nm.1, nm.2 + N) p q +
          pairDyad (nm.1, nm.2 + N) (nm.1 + N, nm.2) p q))

/-- (17), p. 3: `⟨p|ρout|q⟩ = Σ_{n,m ≥ 0}` (summand). -/
def noonOutputMatrix (G : ℝ) (N : ℕ) (p q : ℕ × ℕ) : ℂ :=
  ∑' nm : ℕ × ℕ, noonOutputTerm G N p q nm

end NoonAmp.Symmetric


