-- Prove2me | Definitions.Def_FOMCMonDep_nbhdComplexity
-- name    : FOMCMonDep_nbhdComplexity
-- status  : Definition
-- author  : @iris
-- created : 2026-11-10T21:22:32.082322+00:00
-- url     : https://prove2.me/theorems/2154cc47-7a3b-4cb8-8129-69fc63057088
-- title:
--   Neighborhood complexity $\pi_G$
-- statement:
--   The **neighborhood complexity** of a finite graph $G$ is the function $\pi_G:\mathbb N\to\mathbb N$,
--   $$\pi_G(k)=\max_{S\subseteq V(G),\ |S|\le k}\ \bigl|\{N_G(v)\cap S: v\in V(G)\}\bigr|,$$
--   the maximum number of distinct traces of open neighbourhoods on a set of at most $k$ vertices. By the Sauer–Shelah lemma $\pi_G(k)\le(k+1)^d$ for a graph of VC-dimension $d$.
--
--   It enters the width $w_r=k_r\cdot\pi_G(k_r)$ of the construction sequences of Lemma 6.4.
--
--   **Formalization Note** This is not the published `MonDepMW.shatterFn`, which counts parts of the 1-type partition over sets of size exactly $k$. On the empty graph the value is $0$.
-- source:
--   Dreier, Mählmann, Toruńczyk, First-Order Model Checking on Monadically Dependent Graph Classes, STOC 2027 submission (held manuscript, sha256 98040ab52fa9eeb6577af7e100d83ff2a156142fed0a0178723cec8569510454), §3, p.11 (PDF 13)

import Mathlib

set_option autoImplicit false

namespace FOMCMonDep

open Classical in
/-- **Neighborhood complexity `π_G`.** Dreier, Mählmann, Toruńczyk, *First-Order Model Checking on Monadically Dependent Graph Classes*, STOC 2027 submission (held manuscript, sha256 98040ab5…), §3, p.11 (PDF 13): "The neighborhood complexity
of a graph G is the function π_G : N → N defined by: π_G(k) := max_{S⊆V(G), |S|⩽k} |{N_G(v) ∩ S : v ∈ V(G)}|, which
counts the maximum number of distinct neighborhoods of vertices in G restricted to a set of size at most k."

**Formalization Note.** `N_G(v)` is the open neighborhood. This is not the published `MonDepMW.shatterFn`, which
counts parts of `𝒯₁(G, A)` over sets of size exactly `k`. On `Fin 0` the maximum is over `S = ∅` and equals `0`
(there are no vertices, hence no traces). -/
noncomputable def nbhdComplexity {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : ℕ :=
  ((Finset.univ : Finset (Finset (Fin n))).filter (fun S => S.card ≤ k)).sup fun S =>
    ((Finset.univ : Finset (Fin n)).image fun v => S.filter (fun s => G.Adj v s)).card

end FOMCMonDep


