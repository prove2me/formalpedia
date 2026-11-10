-- Prove2me | Definitions.Def_StudentTeacher976_Adaptivity_InputConversion
-- name    : StudentTeacher976_Adaptivity_InputConversion
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-09T10:12:38.052323+00:00
-- url     : https://prove2.me/theorems/f7bcccf8-e38c-4a6d-8f03-0a609e05b6ab
-- title:
--   Raw input blocks and the signed input-size conversion
-- statement:
--   The source distinguishes the decision-input length $n$ from the raw search-input length $m=nk$. Appendix A seeks a positive integer $k$ satisfying
--
--   $$
--   k=g(nk),\qquad h_n(k)=g(nk)-k.
--   $$
--
--   The gap $h_n(k)$ is integer valued, so negative values are preserved. A finite search scans a supplied numerical bound for a positive solution; existence and a polynomial choice of that bound are not assumed.
--
--   The raw-input decoder uses $k=r(m)$ and splits the input into $k$ consecutive blocks of length $m/k$ when $m>0$ and $k$ divides $m$. Other lengths, including the empty input, take a total easy branch. The auxiliary relation requires the canonical encoding of a tuple satisfying the witness relation on decoded inputs, and the unique empty answer on the easy branch. Malformed output encodings fail.
--
--   These definitions preserve the exact length at which the resource function is evaluated. They add no fixed-point, padding, totality, or complexity hypothesis to the goal.
-- source:
--   Ondřej Ježil, Dimitrios Tsintsilidas, STOC 2027 submission #976 (October 2026), §3, input-size convention, p.19 (PDF p.19); Appendix A, displayed equation k = g(n·k), pp.39–40 (PDF pp.39–40); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/976.pdf

import Definitions.Def_StudentTeacher976_Adaptivity_Witness

open QAdvFew.PoQOracle

namespace StudentTeacher976.Adaptivity

/-- Signed h_n(k) from Appendix A, pp.39–40. No truncated natural subtraction. -/
def sizeGap (g : ℕ → ℕ) (n k : ℕ) : ℤ := (g (n * k) : ℤ) - (k : ℤ)

/-- A finite exhaustive search for a positive fixed point, within a supplied numerical
bound. Existence and a polynomial choice of bound are proof obligations, not fields or
hypotheses of Theorem 1.4. Appendix A's displayed equation k=g(n*k), pp.39–40. -/
def scanFixedPoint (g : ℕ → ℕ) (n bound : ℕ) : Option ℕ :=
  (List.range (bound + 1)).find? fun k => decide (0 < k ∧ k = g (n * k))

/-- Decode exactly k consecutive n-bit blocks, with no tuple-encoding overhead in x.
Outside its length condition this is still a total function; only blockInput uses it. -/
def decodeBlocks (n k : ℕ) (x : Word) : List Word :=
  (List.range k).map fun j => (x.drop (j * n)).take n

/-- At a raw length m, the count is r(m) and the block length is m/r(m). Bad lengths,
the empty input and nondivisible lengths take an explicit easy branch, not a promise.
On construction lengths m=n*k with k=r(m), this gives exactly the source tuple X.
§3 p.19, Appendix A pp.39–40. -/
def blockInput (r : ℕ → ℕ) (x : Word) : Option (List Word) :=
  let m := x.length
  let k := resource r m
  if 0 < m ∧ 0 < k ∧ m % k = 0 then some (decodeBlocks (m / k) k x) else none

/-- The actual raw-string auxiliary search relation of §3.1 p.19. Every input string
is included: off-construction inputs have the unique easy answer []; on construction
inputs the output is a canonical encoding of a witness tuple. Malformed output encodings
cannot satisfy the relation. Totality, polynomial boundedness, refutable presentation
and the r+1-round student are subsequent proof obligations, not assumed properties. -/
def auxiliaryRelation {i : ℕ} {L : Language} (W : WitnessPresentation i L)
    (r : ℕ → ℕ) : SearchRelation := fun x y =>
  match blockInput r x with
  | none => y = []
  | some X => ∃ Y, y = tup Y ∧ TupleRelation W X Y

end StudentTeacher976.Adaptivity


