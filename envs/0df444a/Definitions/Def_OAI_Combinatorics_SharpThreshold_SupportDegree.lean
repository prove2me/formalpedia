-- Prove2me | Definitions.Def_OAI_Combinatorics_SharpThreshold_SupportDegree
-- name    : OAI_Combinatorics_SharpThreshold_SupportDegree
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-19T00:08:39.591955+00:00
-- url     : https://prove2.me/theorems/71142ab4-39a3-45f7-927d-9ab80574e099
-- title:
--   Vertices and degrees of an edge family
-- statement:
--   For a finite family $S$ of finite subsets of a type (typically a set of graph edges):
--
--   1. its vertex set is the union of its members,
--   $$
--   V(S)=\bigcup_{e\in S}e ;
--   $$
--   2. the degree of a point $u$ is the number of members containing it, $\deg_S(u)=|\{e\in S:u\in e\}|$.
--
--   The Fourier support of a low-degree coefficient is an edge set. Its vertices and degrees control how often a random vertex block meets it.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/SharpThreshold/SupportDegree.lean

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/SharpThreshold/SupportDegree.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the SharpThreshold mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_SharpThreshold
import Definitions.Def_OAI_Combinatorics_SharpThreshold_Model
import Definitions.Def_OAI_Combinatorics_SharpThreshold_BlockOrbit
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierBasis
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOrthogonality
import Definitions.Def_OAI_Combinatorics_SharpThreshold_FourierOption

namespace OAI

universe u

/-! Elementary support-graph combinatorics, independent of probability. -/

namespace Problem313.SupportCombinatorics

open Finset

variable {α : Type u} [DecidableEq α]

/-- The non-isolated vertices of a finite edge family. -/
def vertices (S : Finset (Finset α)) : Finset α := S.biUnion id

/-- The number of support edges incident to a vertex. -/
def degree (S : Finset (Finset α)) (u : α) : ℕ :=
  (S.filter (fun e => u ∈ e)).card

end Problem313.SupportCombinatorics

end OAI


