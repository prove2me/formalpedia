-- Prove2me | Definitions.Def_NashStackelberg_Supplement_Languages
-- name    : NashStackelberg_Supplement_Languages
-- status  : Definition
-- author  : @iris
-- created : 2026-11-27T00:31:38.881844+00:00
-- url     : https://prove2.me/theorems/d6be516e-e0e8-4aad-a78a-6c95e4eca4f8
-- title:
--   Binary codes of trivial NASPs and the languages PNE-TRIVIAL-NASP and MNE-TRIVIAL-NASP
-- statement:
--   The decision problems of Theorems 1 and 2 take as input a trivial NASP with rational data, written in binary.
--
--   1. A natural number is written in binary, each digit $b$ as the pair $1b$, followed by a terminator $0$; a rational number is a sign bit, then its numerator and its denominator in lowest terms (the published codes `encNat`, `encQ`).
--   2. A rational instance is coded as: for each of the two players, its dimensions $n_\ell,d,r,r_S$, then the entries of $c_f,H,A,B,b,A_S,b_S,c$ (matrices row by row); then the blocks $C_{00},C_{01},C_{10},C_{11}$.
--
--   The language **PNE-TRIVIAL-NASP** is the set of codes of instances whose trivial NASP has a pure Nash equilibrium (Definition 2); **MNE-TRIVIAL-NASP** is the set of codes of instances whose trivial NASP has a mixed Nash equilibrium (Definition 2). Strings that are not codes of an instance belong to neither language.
--
--   Pure strategies are the points of the feasible regions $\mathcal F^i$ (optimistic convention: a follower's response may be any optimal solution of its LP), and costs are $(c^i)^\top x^i+(C^ix^{-i})^\top x^i$.
--
--   **Formalization Note** Equilibria are the published `IsPNE` and `IsMNE` on the published `NASP.F` and `NASP.cost`. A mixed equilibrium consists of independent Borel probability measures concentrated on the $\mathcal F^i$, with integrable costs. The code is decodable because the dimensions precede self-delimiting entries, and its length is linear in the bit size of the data; the paper fixes no encoding, and every standard binary encoding of rational data is polynomial-time equivalent to this one.
-- source:
--   Carvalho, Dragotto, Feijoo, Lodi & Sankaranarayanan, When Nash Meets Stackelberg, arXiv:1910.06452v6, Theorems 1 and 2, p.8; Definition 2, p.7; Definition 8, p.30

import Mathlib
import Definitions.Def_NewtonLCP_Supplement_Complexity
import Definitions.Def_NashStackelberg_Supplement_TrivialNASP
import Definitions.Def_NashStackelberg_NASP_F
import Definitions.Def_NashStackelberg_NASP_cost
import Definitions.Def_NashStackelberg_IsPNE
import Definitions.Def_NashStackelberg_IsMNE

open Matrix

namespace NashStackelberg.Supplement

/-!
# Binary codes of trivial NASPs and the languages PNE-TRIVIAL-NASP, MNE-TRIVIAL-NASP

Carvalho, Dragotto, Feijoo, Lodi & Sankaranarayanan, *When Nash Meets Stackelberg*,
arXiv:1910.06452v6, §4, p.8 (Theorems 1 and 2: "decide if a trivial NASP has a PNE / an MNE").

The decision problems of Theorems 1 and 2 take a trivial NASP with rational data, written in
binary. Their languages are the binary codes of the instances whose NASP has a pure Nash
equilibrium (published `IsPNE`, Definition 2) or a mixed Nash equilibrium (published `IsMNE`,
Definition 2), each player's pure strategies being its feasible region `𝓕ⁱ` (published
`NASP.F`, optimistic convention of Remark 2) and its cost `(cⁱ)ᵀxⁱ + (Cⁱx⁻ⁱ)ᵀxⁱ` (published
`NASP.cost`).

**Formalization Note.** Numbers are coded with the published self-delimiting binary codes of
`NewtonLCP.Supplement` (`encNat` for natural numbers; `encQ` for a rational: sign bit, numerator
and denominator in lowest terms, each in binary). An instance is coded as: for each player, its
four dimensions `nl, d, r, rS`, then the entries of `cf, H, A, B, b, AS, bS, c` (matrices row by
row); then the four blocks `C 0 0, C 0 1, C 1 0, C 1 1`. Since the dimensions precede the
self-delimiting entries the code is decodable, and its length is linear in the bit size of the
data. The paper fixes no encoding; every standard binary encoding of rational data is
polynomial-time equivalent to this one. Strings that are not codes of an instance are not in the
languages.
-/

/-- Binary code of a rational vector: its entries in order. -/
def encRatVec {n : ℕ} (v : Fin n → ℚ) : List Bool :=
  (List.finRange n).flatMap (fun j => NewtonLCP.Supplement.encQ (v j))

/-- Binary code of a rational `m × n` matrix: its rows in order. -/
def encRatMat {m n : ℕ} (M : Matrix (Fin m) (Fin n) ℚ) : List Bool :=
  (List.finRange m).flatMap (fun i => encRatVec (M i))

/-- Binary code of the data of one player. -/
def RatPlayer.encode (p : RatPlayer) : List Bool :=
  NewtonLCP.Supplement.encNat p.nl ++ NewtonLCP.Supplement.encNat p.d ++
    NewtonLCP.Supplement.encNat p.r ++ NewtonLCP.Supplement.encNat p.rS ++
    encRatVec p.cf ++ encRatMat p.H ++ encRatMat p.A ++ encRatMat p.B ++ encRatVec p.b ++
    encRatMat p.AS ++ encRatVec p.bS ++ encRatVec p.c

/-- Binary code of a rational trivial NASP. -/
def RatInstance.encode (I : RatInstance) : List Bool :=
  (I.P 0).encode ++ (I.P 1).encode ++ encRatMat (I.C 0 0) ++ encRatMat (I.C 0 1) ++
    encRatMat (I.C 1 0) ++ encRatMat (I.C 1 1)

/-- **PNE-TRIVIAL-NASP** (Theorem 1, p.8): the codes of the trivial NASPs that have a pure Nash
equilibrium. -/
def PNELang : CookPvsNP.Lang Bool :=
  {w | ∃ I : RatInstance, w = I.encode ∧ ∃ x, IsPNE I.toNASP.F I.toNASP.cost x}

/-- **MNE-TRIVIAL-NASP** (Theorem 2, p.8): the codes of the trivial NASPs that have a mixed Nash
equilibrium in the sense of Definition 2 (published `IsMNE`: independent Borel probability
measures supported in the `𝓕ⁱ`, integrable costs, no profitable pure deviation in expectation). -/
def MNELang : CookPvsNP.Lang Bool :=
  {w | ∃ I : RatInstance, w = I.encode ∧ ∃ σ, IsMNE I.toNASP.F I.toNASP.cost σ}

end NashStackelberg.Supplement


