-- Prove2me | Definitions.Def_ModernOnlineLearning_ToX_Rademacher
-- name    : ModernOnlineLearning_ToX_Rademacher
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-10-09T02:39:17.844802+00:00
-- url     : https://prove2.me/theorems/8692506f-6ed3-47c3-939e-47cccbb6d645
-- title:
--   Definition 16.1 — empirical Rademacher complexity for bounded linear classes
-- statement:
--   Fix a positive horizon $T$, a sample $z_1,\ldots,z_T\in\mathbb R^d$, and a nonempty bounded set $V\subseteq\mathbb R^d$. A **Rademacher sign** takes the values $-1$ and $1$ with equal probability, independently on each round. The empirical Rademacher complexity of the linear class $H_{\mathrm{lin}}=\{z\mapsto\langle x,z\rangle:x\in V\}$ is
--
--   $$
--   \widehat{\mathfrak R}_S(H_{\mathrm{lin}})=\frac1T\mathbb E_\varepsilon\left[\sup_{x\in V}\sum_{t=1}^T\varepsilon_t\langle x,z_t\rangle\right].
--   $$
--
--   This quantity measures how well a fixed linear predictor in $V$ can fit independent random signs on the sample. The module also defines the coordinate maximum used in Corollary 16.7 and the probability simplex.
--
--   **Formalization Note** Rounds have indices $1,\ldots,T$. The sign expectation is the exact finite average over $2^T$ Boolean sign assignments. The nonempty bounded domain argument ensures the real supremum has its mathematical value; both averages require $T\ge1$. The coordinate maximum also requires $d\ge1$.
-- source:
--   Orabona, arXiv:1912.13213v10, Definition 16.1, pp. 270–271 (display 16.2), and H_lin, p. 271

import Mathlib

namespace ModernOnlineLearning.ToX

/-- The rounds `1, ..., T`; index zero is never used. -/
abbrev Round (T : ℕ) := {t : ℕ // t ∈ Finset.Icc 1 T}

/-- A Rademacher sign encoded by a Boolean. -/
def sign {T : ℕ} (ε : Round T → Bool) (t : Round T) : ℝ :=
  if ε t then 1 else -1

/-- The coordinate pairing on `ℝ^d`. -/
def pairing {d : ℕ} (x z : Fin d → ℝ) : ℝ :=
  ∑ i, x i * z i

/-- The signed supremum over a nonempty bounded linear class, with its actual real value. -/
noncomputable def signedLinearSup {d T : ℕ} (V : Set (Fin d → ℝ))
    (_hV : V.Nonempty ∧ Bornology.IsBounded V) (z : ℕ → Fin d → ℝ)
    (ε : Round T → Bool) : ℝ :=
  sSup {a : ℝ | ∃ x ∈ V, a = ∑ t : Round T, sign ε t * pairing x (z t)}

/-- Definition 16.1, specialized to the bounded linear class `H_lin` of p. 271.
The sign expectation is the exact average over all `2^T` choices. -/
noncomputable def empiricalRadLinear {d T : ℕ} (V : Set (Fin d → ℝ))
    (_hT : 1 ≤ T) (hV : V.Nonempty ∧ Bornology.IsBounded V)
    (z : ℕ → Fin d → ℝ) : ℝ :=
  (1 / (T : ℝ)) * (1 / (2 : ℝ) ^ T) *
    ∑ ε : Round T → Bool, signedLinearSup V hV z ε

/-- The maximum in Corollary 16.7, averaged over all Rademacher signs. -/
noncomputable def empiricalRadMax {d T : ℕ} [NeZero d]
    (_hT : 1 ≤ T) (z : ℕ → Fin d → ℝ) : ℝ :=
  (1 / (T : ℝ)) * (1 / (2 : ℝ) ^ T) *
    ∑ ε : Round T → Bool,
      Finset.univ.sup' Finset.univ_nonempty
        (fun i : Fin d => ∑ t : Round T, sign ε t * z t i)

/-- The probability simplex `Δ^{d-1}`. -/
def simplex (d : ℕ) : Set (Fin d → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i = 1}

end ModernOnlineLearning.ToX


