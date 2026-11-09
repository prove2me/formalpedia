-- Prove2me | Definitions.Def_QCSepTotal_RandProtocol
-- name    : QCSepTotal_RandProtocol
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T08:32:49.200274+00:00
-- url     : https://prove2.me/theorems/c9358809-039d-4298-a079-a6a254c4752f
-- title:
--   Randomized protocols, cost $CC(\Pi)$, error, distributional error, transcripts and $R(F)$
-- statement:
--   A **randomized communication protocol** $\Pi$ between Alice, holding $x\in X$, and Bob, holding $y\in Y$, consists of
--
--   1. finite sets of public coins, of Alice's private coins and of Bob's private coins, drawn independently from given distributions;
--   2. for each value $r$ of the public coins, a deterministic protocol tree in which Alice's messages depend on $x$ and her private coins, and Bob's on $y$ and his private coins.
--
--   The output $\Pi(x,y)$ is the label of the leaf reached. The **communication cost** $CC(\Pi)$ is the maximum number of bits exchanged over all inputs and all outcomes of the randomness; shared random bits are not counted. $\Pi$ **computes** a partial function $F$ with error $\varepsilon$ if $\Pr[\Pi(x,y)\neq F(x,y)]\le\varepsilon$ for every $(x,y)\in\mathrm{dom}(F)$, the probability being over all protocol randomness. For a distribution $\mu$ supported on $\mathrm{dom}(F)$ the **distributional error** is
--   $$\mathrm{err}_\mu(\Pi)=\mathbb E_{(x,y)\sim\mu}\Pr[\Pi(x,y)\neq F(x,y)].$$
--   The **transcript** of $\Pi$ on $(x,y)$ consists of the public coins and the communicated messages; $T_{x,y}$ denotes its distribution. Finally,
--   $$R(F)=\min\{CC(\Pi) : \Pi \text{ computes } F \text{ with error at most } 1/3\}.$$
--
--   These are the objects of the randomized lower bound, Theorem 4.1, and of clause $R(F_{\mathrm{tot}})=\tilde\Omega(R(F))$ of Theorem 1.4.
--
--   **Formalization Note** Protocol trees are the published deterministic two-party trees (`DetCCHard.Protocol`). The output is the leaf label, known to both parties; a final private computation of one party can be appended as one more bit, and with this convention the protocol in which Alice sends $x$ and Bob replies $F(x,y)$ has cost $n+1$, as used on p.7. Coin sets are finite. The maximum in $CC(\Pi)$ is over all values of the coin sets. On finite inputs the set of admissible costs is never empty, so the minimum exists.
-- source:
--   Le Gall, Improved Separations between Quantum and Classical Communication Complexity of Total Functions, arXiv:2609.16726 (held version, sha256 970e1476…), §2, p.5 (randomized communication complexity, $CC(\Pi)$, $\mathrm{err}_\mu$, $\mathrm{err}$); Fact 1, p.5 (transcript distribution); p.1 (R(f))

import Mathlib
import Definitions.Def_DetCCHard_Protocol
import Definitions.Def_QCSepTotal_tv
import Definitions.Def_QCSepTotal_PartialFn

namespace QCSepTotal

/-- The bits sent along the run of a deterministic protocol tree on `(x, y)`, in order (the
communicated messages of F. Le Gall, *Improved Separations between Quantum and Classical
Communication Complexity of Total Functions*, arXiv:2609.16726, held version sha256 970e1476…,
§2, p.5). Its length is the number of bits exchanged. -/
def trace {X Y : Type} : DetCCHard.Protocol X Y → X → Y → List Bool
  | .leaf _, _, _ => []
  | .alice f p₀ p₁, x, y => if f x then true :: trace p₁ x y else false :: trace p₀ x y
  | .bob g p₀ p₁, x, y => if g y then true :: trace p₁ x y else false :: trace p₀ x y

/-- A **randomized communication protocol** with public and private randomness (arXiv:2609.16726,
held version sha256 970e1476…, §2, p.5: "Randomized communication complexity `R(f)` allows
public randomness and arbitrarily many messages").

* `Pub`, `PrivA`, `PrivB` are the finite types of public coins, Alice's private coins and Bob's
  private coins, drawn independently from `μ`, `μA`, `μB`.
* For each public coin `r`, `tree r` is a deterministic protocol tree (`DetCCHard.Protocol`) in
  which Alice holds her input together with her private coins and Bob holds his input together
  with his private coins.

**Formalization Note.** The output is the label of the leaf reached, which both parties know (the
transcript-determined output convention); a party's final private computation can always be
appended as one more bit, and with this convention the trivial protocol has cost `n + 1`, as used
on p.7 (`R(F) ≤ n + 1`). Coin types live in `Type` and are finite, so that `R` below is one
infimum over a single type of protocols. -/
structure RandProtocol (X Y : Type) where
  /-- public coins -/
  Pub : Type
  /-- Alice's private coins -/
  PrivA : Type
  /-- Bob's private coins -/
  PrivB : Type
  [instPub : Fintype Pub]
  [instPrivA : Fintype PrivA]
  [instPrivB : Fintype PrivB]
  /-- law of the public coins -/
  μ : PMF Pub
  /-- law of Alice's private coins -/
  μA : PMF PrivA
  /-- law of Bob's private coins -/
  μB : PMF PrivB
  /-- the deterministic protocol run for each value of the public coins -/
  tree : Pub → DetCCHard.Protocol (X × PrivA) (Y × PrivB)

attribute [instance] RandProtocol.instPub RandProtocol.instPrivA RandProtocol.instPrivB

namespace RandProtocol

variable {X Y : Type}

/-- The joint law of all protocol randomness: public coins, Alice's and Bob's private coins,
independent. -/
noncomputable def coins (P : RandProtocol X Y) : PMF (P.Pub × P.PrivA × P.PrivB) :=
  prodLaw P.μ (prodLaw P.μA P.μB)

/-- The output `Π(x, y)` for a given outcome `ω` of the randomness: the leaf label. -/
def output (P : RandProtocol X Y) (x : X) (y : Y) (ω : P.Pub × P.PrivA × P.PrivB) : Bool :=
  (P.tree ω.1).eval (x, ω.2.1) (y, ω.2.2)

/-- `Pr[Π(x, y) ≠ b]`, the probability over all protocol randomness that the output differs
from `b`. -/
noncomputable def errProb (P : RandProtocol X Y) (x : X) (y : Y) (b : Bool) : ℝ :=
  prob P.coins {ω | P.output x y ω ≠ b}

/-- The **communication cost** `CC(Π)` (p.5): the maximum number of bits exchanged over all
inputs and all outcomes of the randomness; shared random bits are not counted.

**Formalization Note.** The maximum runs over every value of the (finite) coin types. -/
def cost [Fintype X] [Fintype Y] (P : RandProtocol X Y) : ℕ :=
  Finset.univ.sup fun z : X × Y × P.Pub × P.PrivA × P.PrivB =>
    (trace (P.tree z.2.2.1) (z.1, z.2.2.2.1) (z.2.1, z.2.2.2.2)).length

/-- `Π` **computes** the partial function `F` with error at most `ε`: on every promised input
`(x, y) ∈ dom(F)` with `F(x, y) = b`, `Pr[Π(x, y) ≠ b] ≤ ε` (p.5). For a total function this is
every input. -/
def Computes (P : RandProtocol X Y) (F : PartialFn X Y) (ε : ℝ) : Prop :=
  ∀ x y b, F x y = some b → P.errProb x y b ≤ ε

/-- The **distributional error** `err_µ(Π) = E_{(x,y)∼µ} Pr[Π(x, y) ≠ F(x, y)]` (p.5), for a
distribution `µ` supported on `dom(F)`.

**Formalization Note.** Pairs outside `dom(F)` contribute `0`; for `µ` supported on `dom(F)`
they carry weight `0` anyway. -/
noncomputable def distErr [Fintype X] [Fintype Y] (P : RandProtocol X Y) (F : PartialFn X Y)
    (ν : PMF (X × Y)) : ℝ :=
  ∑ p : X × Y, (ν p).toReal * (F p.1 p.2).elim 0 (fun b => P.errProb p.1 p.2 b)

/-- The distribution `T_{x,y}` of the communicated messages and public coins of `Π` on the fixed
input pair `(x, y)` (Fact 1, p.5). Private coins are not part of it. -/
noncomputable def transcriptLaw (P : RandProtocol X Y) (x : X) (y : Y) :
    PMF (P.Pub × List Bool) :=
  P.coins.map fun ω => (ω.1, trace (P.tree ω.1) (x, ω.2.1) (y, ω.2.2))

end RandProtocol

/-- The **randomized communication complexity** `R(F)` (pp.1, 5): the least worst-case cost of a
randomized protocol (public coins, arbitrarily many messages) with error at most `1/3` on every
promised input.

**Formalization Note.** `sInf` of an empty set of naturals is `0`; the set is never empty, since
on finite inputs Alice can send her whole input and Bob the answer. -/
noncomputable def R {X Y : Type} [Fintype X] [Fintype Y] (F : PartialFn X Y) : ℕ :=
  sInf {C : ℕ | ∃ P : RandProtocol X Y, P.Computes F (1 / 3) ∧ P.cost ≤ C}

end QCSepTotal


