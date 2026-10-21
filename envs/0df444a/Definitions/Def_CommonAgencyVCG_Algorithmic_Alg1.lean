-- Prove2me | Definitions.Def_CommonAgencyVCG_Algorithmic_Alg1
-- name    : CommonAgencyVCG_Algorithmic_Alg1
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-21T00:22:49.471168+00:00
-- url     : https://prove2.me/theorems/bf689bf7-b5ce-45d9-bd5e-4f1546122db2
-- title:
--   §3.3–§4.1, pp. 13–20 — L_a, k_a, h^ℓ (LP1), m^ℓ(b), admissible LP2/LP3 solutions, contract ALG1
-- statement:
--   This file defines the quantities behind the algorithmic IIVCG contract of §4.
--
--   Fix a common agency setting (see the Setting definition), and write $b^{-\ell}$ for the bids of the principals other than $\ell$.
--
--   1. For an action $a$, the set of non-negative payment vectors **implementing** $a$ is (p. 13)
--   $$\mathcal L_a = \Big\{ w \in \mathbb R^m_{\ge 0} \;\Big|\; a \in \arg\max_{a'} \{\mathbb E_{o\sim F_{|a'}}[w(o)] - \psi(a')\} \Big\}.$$
--   2. $k_a = \min_{w\in\mathcal L_a} \mathbb E_{o\sim F_{|a}}[w(o)]$ (Claim 2), the cheapest expected payment implementing $a$.
--   3. $h^\ell(b^{-\ell}) = \min_{\tilde v^\ell\in\mathcal V^\ell} \mathrm{Wel}^{a^*(b^{-\ell},\tilde v^\ell)}(b^{-\ell},\tilde v^\ell)$ (Claim 3 (1); the value of LP1, Proposition 3).
--   4. $m^\ell(b) = h^\ell(b^{-\ell}) - \mathrm{Wel}^{a^*(b)}(b^{-\ell},\mathbf 0)$ (Claim 1), an upper bound on principal $\ell$'s expected payment under IR.
--   5. An **admissible selection** chooses for every $b\in\mathcal V$ a vector $w^b \in \arg\min_{w\in\mathcal L_{a^*(b)}} \mathbb E_{o\sim F_{|a^*(b)}}[w(o)]$ (an optimal solution of LP2) and weights $x^b_\ell$ with $0\le x^b_\ell$, $x^b_\ell\, k_{a^*(b)} \le m^\ell(b)$ and $\sum_\ell x^b_\ell = 1$ (Claim 3 (2); an optimal solution of LP3).
--   6. **Contract ALG1** (Definition 4, Algorithm 1 line 8) pays
--   $$t^\ell(b,o) = h^\ell - \big\{F_{|a^*(b)}\cdot(b^{-\ell} + x^b_\ell\, w^b) - \psi(a^*(b))\big\} + x^b_\ell\, w^b(o).$$
--
--   The main theorem of the mission says that ALG1 is IIVCG, LL and IR whenever any such contract exists.
--
--   **Formalization Note** The paper's minima are real infima (`⨅` over a subtype). In this paper's examples the domains may be unbounded, so the infimum is the faithful reading; both index sets are nonempty and bounded below under the standing assumptions, so no junk value arises. The bracket in line 8 is `Wel S (aStar S b) (Function.update b ℓ (x • w))`, which equals $F_{|a^*(b)}\cdot(b^{-\ell}+x w) - \psi(a^*(b))$ with $b^{-\ell}$ read as the sum vector of LP1. Algorithm 1 leaves the choice among optimal LP solutions open, so `alg1` is parametrized by the selections `wsel`, `xsel`, and `ValidSel` states admissibility. Line 5's "Impossible" branch is not modelled.
-- source:
--   Alon, Lavi, Shamash, Talgam-Cohen, Incomplete Information VCG Contracts for Common Agency, arXiv:2105.14998v1, p. 13 (L_a), p. 16 Definition 4, p. 17 Claim 1 (m^ℓ) and Proposition 3 (LP1), p. 18 Claim 2 (k_a), Proposition 4 (LP2), Claim 3, p. 19 Observation 3 (LP3), p. 20 Algorithm 1 line 8

import Mathlib
import Definitions.Def_CommonAgencyVCG_Algorithmic_Setting

namespace CommonAgencyVCG.Algorithmic

variable {n : ℕ} {A O : Type} [Fintype A] [Nonempty A] [Fintype O]

/-- `L_a` (§3.3, p. 13): the non-negative payment vectors `w` under which `a` maximizes
`E_{o∼F|a'}[w(o)] − ψ(a')`. -/
def implSet (S : Setting n A O) (a : A) : Set (O → ℝ) :=
  {w | (∀ o, 0 ≤ w o) ∧ ∀ a', E S a' w - S.psi a' ≤ E S a w - S.psi a}

/-- `k_a = min_{w ∈ L_a} E_{o∼F|a}[w(o)]` (Claim 2, p. 18), as a real infimum. -/
noncomputable def kCost (S : Setting n A O) (a : A) : ℝ :=
  ⨅ w : implSet S a, E S a w

/-- `h^ℓ(b^{−ℓ}) = min_{ṽ^ℓ ∈ V^ℓ} Wel^{a*(b^{−ℓ},ṽ^ℓ)}(b^{−ℓ}, ṽ^ℓ)` (Claim 3 (1), p. 18; the value
of LP1, p. 17), as a real infimum. -/
noncomputable def hAlg (S : Setting n A O) (ℓ : Fin n) (b : Fin n → O → ℝ) : ℝ :=
  ⨅ v : S.V ℓ, Wel S (aStar S (Function.update b ℓ v)) (Function.update b ℓ v)

/-- `m^ℓ(b) = min_{ṽ^ℓ ∈ V^ℓ} Wel^{a*(b^{−ℓ},ṽ^ℓ)}(b^{−ℓ}, ṽ^ℓ) − Wel^{a*(b)}(b^{−ℓ}, 0)`
(Claim 1, p. 17). -/
noncomputable def mBound (S : Setting n A O) (ℓ : Fin n) (b : Fin n → O → ℝ) : ℝ :=
  hAlg S ℓ b - Wel S (aStar S b) (Function.update b ℓ 0)

/-- Admissible outputs of LP2 and LP3 at every in-domain bid profile (Claim 3 (2), p. 18):
`wsel b = w^b ∈ argmin_{w ∈ L_{a*(b)}} E_{o∼F|a*(b)}[w(o)]`, and `xsel b = x^b` with `0 ≤ x^b_ℓ`,
`x^b_ℓ · k_{a*(b)} ≤ m^ℓ(b)` and `∑_ℓ x^b_ℓ = 1`. -/
def ValidSel (S : Setting n A O) (wsel : (Fin n → O → ℝ) → O → ℝ)
    (xsel : (Fin n → O → ℝ) → Fin n → ℝ) : Prop :=
  ∀ b, InDom S b →
    wsel b ∈ implSet S (aStar S b) ∧ E S (aStar S b) (wsel b) = kCost S (aStar S b) ∧
      (∀ ℓ, 0 ≤ xsel b ℓ ∧ xsel b ℓ * kCost S (aStar S b) ≤ mBound S ℓ b) ∧ ∑ ℓ, xsel b ℓ = 1

/-- Contract ALG1 (Definition 4, p. 16), Algorithm 1 line 8 (p. 20), for the LP selections
`wsel`, `xsel`:
`t^ℓ(b, o) = h^ℓ − {F|a*(b) · (b^{−ℓ} + x^b_ℓ w^b) − ψ(a*(b))} + x^b_ℓ w^b(o)`. -/
noncomputable def alg1 (S : Setting n A O) (wsel : (Fin n → O → ℝ) → O → ℝ)
    (xsel : (Fin n → O → ℝ) → Fin n → ℝ) : Contract n O := fun b ℓ o =>
  hAlg S ℓ b - Wel S (aStar S b) (Function.update b ℓ (xsel b ℓ • wsel b)) + xsel b ℓ * wsel b o

end CommonAgencyVCG.Algorithmic


