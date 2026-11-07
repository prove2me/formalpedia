-- Prove2me | Definitions.Def_MonoTestDAG_numTC
-- name    : MonoTestDAG_numTC
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T21:08:24.938194+00:00
-- url     : https://prove2.me/theorems/82095740-4278-4e3f-9f0d-c4ef88e4a3ee
-- title:
--   The transitive closure $E(\mathrm{TC}(G))$ and $\ell$
-- statement:
--   For a directed graph $G=(V,E)$, the transitive closure contains only nontrivial comparable pairs:
--   $$
--   E(\mathrm{TC}(G)):=\{(u,v)\in V\times V: u\ne v\ \text{and}\ u\leadsto v\},
--   $$
--   and $\ell:=|E(\mathrm{TC}(G))|$.
--
--   **Formalization Note.** The diagonal is excluded, as on the page. The module also defines the finite set `tcPairs`.
-- source:
--   Yoshida, Testing Monotonicity of Real-Valued Functions on DAGs, arXiv:2602.15341 (sha256 454609db…), §2.1, p.10

import Mathlib
import Definitions.Def_MonoTestDAG_Reach

namespace MonoTestDAG

open Classical in
/-- The edge set `E(TC(G)) = {(u, v) ∈ V × V : u ≠ v and u ⇝ v}` of the transitive closure of `G`.
Transitive closures contain only nontrivial comparable pairs (no diagonal).

Yoshida, *Testing Monotonicity of Real-Valued Functions on DAGs*, arXiv:2602.15341
(sha256 454609db…), §2.1, p.10. -/
noncomputable def tcPairs {V : Type} [Fintype V] (E : V → V → Prop) : Finset (V × V) :=
  Finset.univ.filter (fun p => p.1 ≠ p.2 ∧ Reach E p.1 p.2)

/-- `ℓ := |E(TC(G))|`, the number of edges of the transitive closure (the number of comparable
pairs). Yoshida, arXiv:2602.15341 (sha256 454609db…), §1.1–1.2, p.1 and §2.1, p.10. -/
noncomputable def numTC {V : Type} [Fintype V] (E : V → V → Prop) : ℕ :=
  (tcPairs E).card

end MonoTestDAG


