-- Prove2me | Definitions.Def_CEPolytopeHard_encodeDist
-- name    : CEPolytopeHard_encodeDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T17:16:39.692364+00:00
-- url     : https://prove2.me/theorems/7bf1502c-2e3a-4e59-a5da-cedf9e22d6ce
-- title:
--   Encoding of finite-support distributions over rational profiles
-- statement:
--   An answer of the correlated-equilibrium problem is a finite list $L = ((w_1, p_1), \dots, (w_K, p_K))$ of rational weights $w_k$ and rational profiles $p_k$ (one rational vector per player), written in binary as a length-prefixed list. The listed distribution is
--   $$
--   \mu_L = \sum_{k=1}^K w_k\, \delta_{p_k},
--   $$
--   so the weights of repeated profiles are added. A listed profile has the **shape** of a game $G$ when it has one vector per player and player $i$'s vector has $d_i$ entries.
--
--   This is the output form of Section 2.1: "finite-support distributions $\mu$, represented by listing the elements of the support set and their probabilities", with all numbers rational.
-- source:
--   Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, The Complexity of Correlated Equilibria Beyond Normal-Form Games, arXiv:2605.17665 (held version of November 2, 2026, sha256 6aec500a…7820), Section 2.1, p.10

import Mathlib
import Definitions.Def_CorrelatedAuctionComplexity_Main_BinaryCodec
import Definitions.Def_CEPolytopeHard_lenList
import Definitions.Def_CEPolytopeHard_MLGame

set_option autoImplicit false

namespace CEPolytopeHard

open CorrelatedAuctionComplexity.Main

/-- The **binary encoding of a finite-support distribution** over rational profiles
(Anagnostides–Daskalakis–Farina–Golowich–Sandholm–Zhang, *The Complexity of Correlated
Equilibria Beyond Normal-Form Games*, arXiv:2605.17665, held version of November 2, 2026, sha256
6aec500a…7820, Section 2.1, p.10: "we will consider only finite-support distributions μ,
represented by listing the elements of the support set and their probabilities", with "All
numbers are rational numbers encoded in binary"). An answer is a list of pairs
`(weight, profile)`, a profile being the list of the players' rational strategy vectors; it is
written as a length-prefixed list of (rational weight, length-prefixed list of length-prefixed
rational vectors), with the public `ratCode` and `pack`. -/
def encodeDist (L : List (ℚ × List (List ℚ))) : Bits :=
  pack (lenList (fun e => ratCode e.1 ++ lenList (lenList ratCode) e.2) L)

namespace MLGame

/-- a listed rational profile `p` has the shape of `G`: one vector per player, of length `d_i` -/
def Shaped (G : MLGame) (p : List (List ℚ)) : Prop :=
  p.length = G.n ∧ ∀ i : Fin G.n, (p.getD i.val []).length = G.dim i

/-- the real profile of a listed rational profile -/
def ratProfile (G : MLGame) (p : List (List ℚ)) : G.Profile :=
  fun i c => (((p.getD i.val []).getD c.val 0 : ℚ) : ℝ)

/-- the distribution listed by `L`: weights of equal profiles are merged (summed) -/
noncomputable def distOf (G : MLGame) (L : List (ℚ × List (List ℚ))) : G.Profile →₀ ℝ :=
  (L.map fun e => Finsupp.single (G.ratProfile e.2) (e.1 : ℝ)).sum

end MLGame

end CEPolytopeHard


