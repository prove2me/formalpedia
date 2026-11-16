-- Prove2me | Definitions.Def_FiniteGroupTesting_LinearQuery_Supplement_Dictionary
-- name    : FiniteGroupTesting_LinearQuery_Supplement_Dictionary
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T20:16:51.729203+00:00
-- url     : https://prove2.me/theorems/7e9fce12-4c47-4bd9-9860-1454d1fe554b
-- title:
--   Syntactic inverses, dictionary walks and common locators
-- statement:
--   For an arbitrary operation $*$ on $n$ labels, each inverse candidate is the fixed binary-power expression for $s_i^{n-1}$; it is not assumed to be an inverse. The visible signed labels are $u_i=s_i$ and $u_{-i}=t_i$. Dictionary walks include their initial point, and a candidate is retained exactly when all equalities among dictionary positions agree in the input and candidate walks.
--
--   For one common signed word $\sigma$, shared across all starting labels and candidates, the locator stops at the first dictionary hit, including time zero. If the hit is reached after the prefix $w$, define
--   $$\Psi_H(x)=\phi_H(x_{\tau(x)})\left(\prod_{j\in w}a_j\right)^{-1};$$
--   otherwise the locator is undefined. The hit record contains the visible endpoint and the word prefix. One oracle program records this visible path without receiving any candidate as input; candidates interpret that record offline. The missed fraction $Z$ counts all starting labels whose common path has no hit. No independence among those starting labels is part of the definition.
-- source:
--   Nader Bshouty, STOC 2027 submission #622 (October 2026), pp. 25–28, Sections 4.1–4.4, equations (4.3.1), (4.4.1), (4.4.4)

import Definitions.Def_FiniteGroupTesting_LinearQuery_Supplement_PartialMaps
import Definitions.Def_FiniteGroupTesting_LinearQuery_OracleRuns

set_option autoImplicit false

namespace FiniteGroupTesting.LinearQuery.Supplement

noncomputable section
attribute [local instance] Classical.propDecidable

/-- One fixed binary powering expression, including on nonassociative tables.
The q<=1 branch is used at q=1 on the stated n>=2 domain. -/
def binaryPower {n : ℕ} (s : Fin n) (q : ℕ) : OracleRun n (Fin n) :=
  if q ≤ 1 then pure s else do
    let v ← binaryPower s (q / 2)
    let w ← OracleRun.ask v v
    if q % 2 = 0 then pure w else OracleRun.ask w s
termination_by q
decreasing_by omega

def powerValue {G : Type*} (op : G → G → G) (s : G) (q : ℕ) : G :=
  if q ≤ 1 then s else
    let v := powerValue op s (q / 2)
    if q % 2 = 0 then op v v else op (op v v) s
termination_by q
decreasing_by omega

def visibleSigned {G : Type*} (op : G → G → G) (n : ℕ) {k : ℕ}
    (s : Fin k → G) (j : Signed k) : G :=
  if j.2 then powerValue op (s j.1) (n - 1) else s j.1

def walk {G : Type*} {k : ℕ} (op : G → G → G) (u : Signed k → G)
    (start : G) (word : List (Signed k)) : List G :=
  word.scanl (fun x j => op x (u j)) start

def equalityPattern {G H : Type*} (ds : List G) (hs : List H) : Prop :=
  ds.length = hs.length ∧ ∀ r s : Fin ds.length,
    ds.get r = ds.get s ↔ hs[r.val]? = hs[s.val]?

def dictionaryValue {G H : Type*} [DecidableEq G] (ds : List G) (hs : List H)
    (x : G) : Option H :=
  ((ds.zip hs).find? fun xy => xy.1 == x).map Prod.snd

/-- A hit records the visible label and exactly the prefix used to reach it. -/
def firstHit {G : Type*} [DecidableEq G] {k : ℕ} (op : G → G → G)
    (u : Signed k → G) (D : List G) (x : G) : List (Signed k) → Option (G × List (Signed k))
  | [] => if x ∈ D then some (x, []) else none
  | j :: rest => if x ∈ D then some (x, []) else
      (firstHit op u D (op x (u j)) rest).map fun hit => (hit.1, j :: hit.2)

def interpretHit {G H : Type*} [DecidableEq G] [Group H] {k : ℕ}
    (ds : List G) (hs : List H) (a : Fin k → H)
    (hit : Option (G × List (Signed k))) : Option H :=
  match hit with
  | none => none
  | some (d, word) => (dictionaryValue ds hs d).map fun h =>
      h * ((word.map (signedMark a)).prod)⁻¹

def locator {G H : Type*} [DecidableEq G] [Group H] {k : ℕ}
    (op : G → G → G) (u : Signed k → G) (ds : List G) (hs : List H)
    (a : Fin k → H) (word : List (Signed k)) (x : G) : Option H :=
  interpretHit ds hs a (firstHit op u ds x word)

def missedFraction {G : Type*} [Fintype G] [DecidableEq G] {k : ℕ}
    (op : G → G → G) (u : Signed k → G) (D : List G) (word : List (Signed k)) : ℝ :=
  uniformProbability fun x => firstHit op u D x word = none

/-- One path is queried once; no candidate group is an argument to this program. -/
def queryHit {n k : ℕ} (u : Signed k → Fin n) (D : List (Fin n))
    (x : Fin n) : List (Signed k) → OracleRun n (Option (Fin n × List (Signed k)))
  | [] => pure (if x ∈ D then some (x, []) else none)
  | j :: rest => if x ∈ D then pure (some (x, [])) else do
      let y ← OracleRun.ask x (u j)
      let hit ← queryHit u D y rest
      pure (hit.map fun h => (h.1, j :: h.2))

def queryWalk {n k : ℕ} (u : Signed k → Fin n) (start : Fin n) :
    List (Signed k) → OracleRun n (List (Fin n))
  | [] => pure [start]
  | j :: rest => do
      let y ← OracleRun.ask start (u j)
      let tail ← queryWalk u y rest
      pure (start :: tail)

end
end FiniteGroupTesting.LinearQuery.Supplement


