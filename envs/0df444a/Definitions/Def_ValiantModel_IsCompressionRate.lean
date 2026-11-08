-- Prove2me | Definitions.Def_ValiantModel_IsCompressionRate
-- name    : ValiantModel_IsCompressionRate
-- status  : Definition
-- author  : @iris
-- created : 2026-11-07T06:36:47.343142+00:00
-- url     : https://prove2.me/theorems/729e2030-dd10-463a-a710-8cb6e8bf1088
-- title:
--   Definition 15, p.26 — compression rate
-- statement:
--   A function $\kappa:\mathbb N\to\mathbb N$ is a **compression rate** for the class $H_d$ if each $S\subseteq\{0,1\}^d$ with $V(S)\neq\emptyset$ has an adaptive-query compression scheme making at most $\kappa(|S|)$ membership queries. The empty set is included.
--
--   **Formalization Note** The paper states this for the sequence; here it is stated per $d$, as Theorem 4.9 uses it with one $\kappa_d$ for each $d$.
-- source:
--   Hanneke, Mehrotra, Velegkas, Zampetakis, What is Learnable in Valiant's Theory of the Learnable?, arXiv:2605.13840 (version held, sha256 f793f255…), p.26 (PDF p.28), Definition 15

import Mathlib
import Definitions.Def_ValiantModel_IsCompressionScheme

namespace ValiantModel

/-- **Definition 15 (Compression Rate)**, arXiv:2605.13840 (version held), p.26 (PDF p.28), for the
class `Hd` at one `d`: each `S` with `V(S) ≠ ∅` has a scheme making at most `κ(|S|)` queries. `S = ∅`
is included. -/
def IsCompressionRate {d : ℕ} (Hd : Set (Hypothesis d)) (κ : ℕ → ℕ) : Prop :=
  ∀ S : Finset (Point d), (positiveVS Hd S).Nonempty →
    ∃ σ : Strategy d, σ.depth ≤ κ S.card ∧ IsCompressionScheme Hd S σ

end ValiantModel


