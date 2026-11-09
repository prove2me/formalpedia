-- Prove2me | Definitions.Def_IPPComplexities_Unconditional_encoding
-- name    : IPPComplexities_Unconditional_encoding
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-08T10:25:00.032542+00:00
-- url     : https://prove2.me/theorems/7d45e788-c3bf-4699-8eec-2d8b12d56330
-- title:
--   A fixed binary interpreter for finitely described verifier strategies
-- statement:
--   One fixed interpreter maps a length $n$ and a finite binary description $s$ to a verifier $\operatorname{decode}_n(s)$. The description contains a finite table for the public next-speaker rule, followed by a finite list of deterministic oracle plans. It is interpreted by uniform private choice from that list, retaining multiplicities. Invalid indices or syntax fail parsing; incompatible plans are discarded, and an empty result rejects. The interpreter has no property or original-verifier parameter.
--
--   Natural numbers use unary prefixes. Plan prefixes specify a verdict, a coordinate query and its two branches, a transmitted bit and its continuation, or a received bit and its two branches. The public table is indexed by the binary heap index of the transcript. All parsing is effective on finite lists; the output distribution is an exactly specified finite rational law. Uniform finite choice may be implemented by fair-bit rejection sampling, with no charge to queries or communication.
--
--   For positive integers $A,D$, the description scale is
--
--   $$B_{A,D}(n,t)=\begin{cases}A,&t=0,\\(A\max\{n,2\})^{Dt},&t>0.\end{cases}$$
--
--   For $n\ge2$ and $t\ge1$ this is precisely $\operatorname{poly}(n)^t$. The constant zero-resource allowance stores an input-independent verdict; it avoids deleting zero-query or zero-communication cases. Only the replacement in Lemma 3.1 is required to lie in this coded class. This definition itself claims neither compression nor validity.
-- source:
--   Noga Amit, Oded Goldreich, STOC 2027 submission #297 (October 2026), pp. 7–8, Lemma 3.1 and its finite-sample description convention (PDF pp. 9–10); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/297.pdf

import Definitions.Def_IPPComplexities_Unconditional_interaction

namespace IPPComplexities.Unconditional

/-- Unary natural: k true bits followed by false. Invalid suffixes fail. -/
def parseNat : List Bool → Option (ℕ × List Bool)
  | [] => none
  | false :: bs => some (0, bs)
  | true :: bs => do
      let (k, rest) ← parseNat bs
      pure (k + 1, rest)

/-- A prefix parser for finite oracle plans. Tags 00/01 are verdicts;
10 is query with unary index and two subplans; 110 is send with its bit
and subplan; 111 is receive with two subplans. Fuel bounds parsing depth. -/
def parsePlan (n : ℕ) : ℕ → List Bool → Option (Plan n × List Bool)
  | 0, _ => none
  | fuel + 1, bs => match bs with
    | false :: b :: rest => some (.halt b, rest)
    | true :: false :: rest => do
        let (i, rest) ← parseNat rest
        if h : i < n then
          let (l, rest) ← parsePlan n fuel rest
          let (r, rest) ← parsePlan n fuel rest
          pure (.query ⟨i, h⟩ l r, rest)
        else none
    | true :: true :: false :: b :: rest => do
        let (s, rest) ← parsePlan n fuel rest
        pure (.send b s, rest)
    | true :: true :: true :: rest => do
        let (l, rest) ← parsePlan n fuel rest
        let (r, rest) ← parsePlan n fuel rest
        pure (.receive l r, rest)
    | _ => none

def parsePlans (n fuel : ℕ) : ℕ → List Bool → Option (List (Plan n) × List Bool)
  | 0, bs => some ([], bs)
  | k + 1, bs => do
      let (s, rest) ← parsePlan n fuel bs
      let (ss, rest) ← parsePlans n fuel k rest
      pure (s :: ss, rest)

/-- Heap index of a public transcript; the empty transcript has index zero. -/
def transcriptIndex (t : List Bool) : ℕ :=
  t.foldl (fun i b => 2 * i + 1 + if b then 1 else 0) 0

/-- Finite table, default verifier-to-prover outside the table. -/
def tableTurn (table : List Bool) : Turn :=
  fun t => table[transcriptIndex t]?.getD true

/-- Filter only malformed plans, without adding any input-dependent test. -/
def checkedPlans {n : ℕ} (turn : Turn) (ss : List (Plan n)) :
    List {s : Plan n // compatible turn s [] = true} :=
  ss.filterMap fun s => if h : compatible turn s [] = true then some ⟨s, h⟩ else none

/-- Uniform choice from the decoded list, including multiplicities.
An empty list gives the deterministic rejecting verifier. -/
noncomputable def sampledVerifier {n : ℕ} (turn : Turn) (ss : List (Plan n)) :
    Verifier n :=
  { turn := turn
    law := match checkedPlans turn ss with
      | [] => PMF.pure ⟨.halt false, rfl⟩
      | s :: rest => (PMF.uniformOfFintype (Fin (rest.length + 1))).map
          (fun i => (s :: rest).get i) }

/-- One fixed interpreter, with no property or verifier parameter. A code has a
unary table length, that many table bits, a unary sample count, and plan codes.
Invalid codes reject. Only finite uniform laws occur in its output. -/
noncomputable def decode (n : ℕ) (code : List Bool) : Verifier n :=
  let parsed : Option (List Bool × List (Plan n)) := do
    let (len, rest) ← parseNat code
    if len ≤ rest.length then
      let table := rest.take len
      let (k, rest) ← parseNat (rest.drop len)
      let (ss, rest) ← parsePlans n (code.length + 1) k rest
      if rest = [] then pure (table, ss) else none
    else none
  match parsed with
  | some (table, ss) => sampledVerifier (tableTurn table) ss
  | none => sampledVerifier (fun _ => true) []

/-- Finite verdict-code overhead at zero resources, ordinary polynomial-exponential
scale otherwise. max n 2 only supplies the two finite exceptional input lengths. -/
def descriptionBound (A D n resources : ℕ) : ℕ :=
  if resources = 0 then A else (A * max n 2) ^ (D * resources)

end IPPComplexities.Unconditional


