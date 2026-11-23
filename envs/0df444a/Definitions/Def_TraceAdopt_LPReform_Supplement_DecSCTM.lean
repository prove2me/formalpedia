-- Prove2me | Definitions.Def_TraceAdopt_LPReform_Supplement_DecSCTM
-- name    : TraceAdopt_LPReform_Supplement_DecSCTM
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-23T05:48:05.855812+00:00
-- url     : https://prove2.me/theorems/efd973c3-44ab-4d84-8ab8-736faee4fdc0
-- title:
--   Definition 1, p. 11 — DEC-SCTM as a binary language with parameters $k$ and $\theta$
-- statement:
--   **DEC-SCTM** is the decision version of the least-costly seed set problem MIN-SCTM in the simplified setting of §4, where all benefits and adoption costs equal one.
--
--   An **input** consists of $n$ firms $N_F=\{1,\dots,n\}$, $m$ supply chains with hyperedges $e_1,\dots,e_m\subseteq N_F$, rational seeding costs $w_1,\dots,w_n\in\mathbb Q$ and an integer budget $h\in\mathbb Z$. For fixed parameters $k\ge1$ and $\theta$, the input is **valid** when
--
--   1. every hyperedge has exactly $k$ firms, $|e_j|=k$;
--   2. the hypergraph is connected (its bipartite firm–chain incidence graph $G'$ is connected);
--   3. every firm belongs to at least one supply chain.
--
--   The SCTM process is that of §3.1 with $r_{ji}=1$, $c_i=1$ and $\theta_j=\theta$: starting from a seed set $S_0$, a firm outside the active set adopts as soon as one of its supply chains contains at least $\theta-1$ other active firms. The answer is YES when some seed set $S_0$ with
--
--   $$\sum_{i\in S_0} w_i\le h$$
--
--   eventually activates every firm.
--
--   The language $\mathrm{DEC\text{-}SCTM}_{k,\theta}\subseteq\{0,1\}^*$ consists of the binary codes of the valid inputs whose answer is YES. A code lists $n$ and $m$, then each hyperedge as its size followed by its firms in increasing order, then each $w_i$ as the numerator (with sign) and positive denominator of its reduced form, then $h$, every number as a self-delimiting binary numeral. Every other word is rejected.
--
--   This language is the object of the complexity classification of Theorem 1 and of Lemma 1.
--
--   **Formalization Note** The instance is the published `TraceAdopt.LPReform.Instance` with `r = 1`, `c = 1`, `θ_j = θ`, and full activation is the published `FullyActivates`. The standing assumption $\theta_j\ge2$ of §3.1 is not imposed, because Theorem 1 has a row $\theta=1$; validity does not use $\theta$. Numerals are the published `OptimalQueuingComplexity.Restless` codes (`encNat`, `encInt`, `encRat`), which are length-faithful.
-- source:
--   Blaettchen, Calmon & Hall, Traceability Technology Adoption in Supply Chain Networks, arXiv:2104.14818v4, p. 11, Definition 1 and the §4 setting (r_ji = c_i = 1, k_j = k, θ_j = θ); pp. 5–6, §3.1 (connectivity, all nodes can become active)

import Mathlib
import Definitions.Def_TraceAdopt_LPReform_Model
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_OptimalQueuingComplexity_Restless_encNat

set_option autoImplicit false

namespace TraceAdopt.LPReform.Supplement

open OptimalQueuingComplexity.Restless

/-- An input of DEC-SCTM (Definition 1, p. 11): firms `Fin n`, supply chains `Fin m` with
hyperedges `e j ⊆ Fin n`, rational seeding costs `w i` and an integer budget `h`. The benefits,
adoption costs and thresholds are not part of the input: `r_ji = c_i = 1` and `θ_j = θ`. -/
structure DecInput where
  n : ℕ
  m : ℕ
  e : Fin m → Finset (Fin n)
  w : Fin n → ℚ
  h : ℤ

/-- The §3.1 instance of a DEC-SCTM input with uniform threshold `θ`:
`r_ji = 1`, `c_i = 1`, `θ_j = θ` for all firms `i` and chains `j`. -/
def DecInput.toInstance (x : DecInput) (θ : ℕ) : Instance where
  n := x.n
  m := x.m
  e := x.e
  r := fun _ _ => 1
  c := fun _ => 1
  θ := fun _ => θ

/-- The hypergraph of `x` is a valid DEC-SCTM hypergraph for chain size `k` (Definition 1 with
§3.1): every hyperedge has exactly `k` firms (`k_j = k`), the hypergraph is connected (p. 5,
read through the auxiliary graph `G′` as in the published model), and every firm lies in some
supply chain (p. 6, "all nodes can become active", which for `r_ji = c_i = 1` says exactly this).
The threshold condition `θ ≤ k` is a condition on the problem parameters, not on the input. -/
def DecInput.Valid (x : DecInput) (k : ℕ) : Prop :=
  (∀ j, (x.e j).card = k) ∧
  (x.toInstance 1).Connected ∧
  (∀ i : Fin x.n, ∃ j, i ∈ x.e j)

/-- The question of DEC-SCTM (Definition 1): is there a seed set `S₀` of cost
`∑_{i ∈ S₀} w_i ≤ h` leading to full SCTM activation? -/
def DecInput.Yes (x : DecInput) (θ : ℕ) : Prop :=
  ∃ S : Finset (Fin x.n), FullyActivates (x.toInstance θ) S ∧ ∑ i ∈ S, x.w i ≤ (x.h : ℚ)

/-- A hyperedge as a binary word: its cardinality, then its firms in increasing order. -/
def encEdge {n : ℕ} (s : Finset (Fin n)) : List Bool :=
  encNat s.card ++ (s.sort (· ≤ ·)).flatMap encFin

/-- The binary code of a DEC-SCTM input: `n`, `m`, the `m` hyperedges, the `n` rational costs
(reduced numerator with sign, positive denominator), and the integer budget, each a
self-delimiting binary numeral. -/
def DecInput.code (x : DecInput) : List Bool :=
  encNat x.n ++ encNat x.m ++ encTable encEdge x.e ++ encTable encRat x.w ++ encInt x.h

/-- **DEC-SCTM with parameters `k` and `θ`** as a language over `{0,1}`: the codes of valid
inputs whose answer is YES. Every other word (malformed, a hyperedge of the wrong size, a
disconnected hypergraph, a firm in no chain, or answer NO) is rejected. -/
def decSCTM (k θ : ℕ) : CookPvsNP.Lang Bool :=
  {s | ∃ x : DecInput, s = x.code ∧ x.Valid k ∧ x.Yes θ}

end TraceAdopt.LPReform.Supplement


