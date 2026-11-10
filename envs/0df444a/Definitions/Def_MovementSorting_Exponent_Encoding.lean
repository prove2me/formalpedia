-- Prove2me | Definitions.Def_MovementSorting_Exponent_Encoding
-- name    : MovementSorting_Exponent_Encoding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-09T21:01:24.637586+00:00
-- url     : https://prove2.me/theorems/bf43e650-71fe-455e-86f2-a55723a43b2e
-- title:
--   Bit encodings for the polynomial-time clauses: planners and box paths
-- statement:
--   Encodings used by the polynomial-time clauses, with every number in unary ($k \mapsto 1^k0$), so that an input carrying $m$ has length at least $m$ and a polynomial in the input length is a polynomial in $n = m^d$ for fixed $d$. A **planner** is one function $f$ on bit strings. The algorithm it defines with coin string $\omega$ (`plannerAlg d m R f ω`) asks $f$, before round $t$, for the next route on the query (tag 1, $m$, $t$, $\omega$, the outcome lists of the earlier rounds), and finally for the output list (query with $t = R$); answers are decoded as lists of configurations or positions given by their 0-based coordinates. `plannerRounds f m` is the number of rounds $f$ announces for $m$ (query tag 0). `plannerExpMove d m R K f π` is the expected movement when $\omega$ is uniform on $\{0,1\}^K$ (fair coins). For Lemma 5.1(i), `encodeBoxInstance` encodes $m'$, a box of $\mathbb{Z}^{D'}$ (lower corner and sides), a start point and the points of $Q$, and `decodeIntPath` decodes a lattice path; `InBox` and `intL1` are box membership and the $\ell_1$ distance.
-- source:
--   Wang (2026), The Movement Complexity of Sorting, arXiv:2611.01157 (held copy SHA-256 90e3d9df…), Theorem 1.1, p. 3 (polynomial-time clause); Lemma 5.1(i), p. 23

import Definitions.Def_MovementSorting_Exponent_Model

set_option autoImplicit false

open scoped ENNReal

namespace MovementSorting.Exponent

/-! # Bit encodings for the polynomial-time clauses (Theorem 1.1, p. 3; Lemma 5.1(i), p. 23)

Every number is written in **unary** (`k ↦ 1^k 0`), so an input carrying `m` has length at least
`m`, and a polynomial in the input length is a polynomial in `n = m^d` for fixed `d`.
A *planner* is one function `f : List Bool → List Bool`; the algorithm it defines asks `f`, before
each round, for the next route given `m`, the round index, its coin string and the outcome lists
of the earlier rounds, and finally for the output list. -/

/-- Unary encoding of a list of naturals: `k ↦ true^k false`. -/
def encodeNats (l : List ℕ) : List Bool := l.flatMap (fun k => List.replicate k true ++ [false])

/-- Decoding of `encodeNats` (a trailing unterminated run is ignored). -/
def decodeNats (l : List Bool) : List ℕ := go l 0
where
  go : List Bool → ℕ → List ℕ
    | [], _ => []
    | true :: l, k => go l (k + 1)
    | false :: l, k => k :: go l 0

/-- Split a list into consecutive chunks of length `k` (`k ≥ 1`; the last may be shorter). -/
def chunks {α : Type} (k : ℕ) (l : List α) : List (List α) := l.toChunks k

/-- A position from `d` coordinates (0-based); `none` if a coordinate is `≥ m` or the length is
wrong. -/
def decodePos (d m : ℕ) (l : List ℕ) : Option (Pos d m) :=
  if h : l.length = d ∧ ∀ i : Fin d, l.getD i 0 < m then some (fun i => ⟨l.getD i 0, h.2 i⟩)
  else none

/-- A configuration from `2d` coordinates (first head, then second head). -/
def decodeConfig (d m : ℕ) (l : List ℕ) : Option (Config d m) :=
  match decodePos d m (l.take d), decodePos d m (l.drop d) with
  | some x, some y => some (x, y)
  | _, _ => none

/-- The route encoded by a planner answer: the decodable configurations, in order. -/
def decodeRoute (d m : ℕ) (out : List Bool) : List (Config d m) :=
  (chunks (2 * d) (decodeNats out)).filterMap (decodeConfig d m)

/-- The output list encoded by a planner answer. -/
def decodePositions (d m : ℕ) (out : List Bool) : List (Pos d m) :=
  (chunks d (decodeNats out)).filterMap (decodePos d m)

/-- The query for round `t` (the round index `t = R` asks for the output): tag `1`, `m`, `t`,
the coin string, and the earlier outcome lists, each length-prefixed. -/
def plannerQuery (m t : ℕ) (ω : List Bool) (h : List (List Bool)) : List Bool :=
  encodeNats ([1, m, t, ω.length] ++ ω.map (fun b => if b then 1 else 0) ++ [h.length] ++
    h.flatMap (fun o => o.length :: o.map (fun b => if b then 1 else 0)))

/-- The number of rounds a planner asks for at `m` (query tag `0`): the first number of its
answer. -/
def plannerRounds (f : List Bool → List Bool) (m : ℕ) : ℕ :=
  (decodeNats (f (encodeNats [0, m]))).headD 0

/-- The `R`-round deterministic algorithm defined by the planner `f` and the coin string `ω`. -/
def plannerAlg (d m R : ℕ) (f : List Bool → List Bool) (ω : List Bool) : DetAlg d m R where
  route t h := decodeRoute d m (f (plannerQuery m t ω h))
  output h := decodePositions d m (f (plannerQuery m R ω h))

/-- `E[Move]` of the planner algorithm with `K` fair coins: `ω` uniform on `{0,1}^K`. -/
noncomputable def plannerExpMove (d m R K : ℕ) (f : List Bool → List Bool) (π : Input d m) :
    ℝ≥0∞ :=
  ∑ ω : Fin K → Bool, ((2 : ℝ≥0∞) ^ K)⁻¹ * ((plannerAlg d m R f (List.ofFn ω)).move π : ℝ≥0∞)

/-! ## Lattice paths in a box of `ℤ^{D'}` (Lemma 5.1(i)) -/

/-- An integer as two unary naturals `(z⁺, z⁻)`. -/
def intParts (z : ℤ) : List ℕ := [z.toNat, (-z).toNat]

/-- The instance of Lemma 5.1(i): `m'`, the box (lower corner `a`, sides `s`), the start point,
and the points of `Q` (as a list), all in unary. -/
def encodeBoxInstance (D' m' : ℕ) (a : Fin D' → ℤ) (s : Fin D' → ℕ) (start : Fin D' → ℤ)
    (Q : List (Fin D' → ℤ)) : List Bool :=
  encodeNats ([m'] ++ (List.ofFn a).flatMap intParts ++ List.ofFn s ++
    (List.ofFn start).flatMap intParts ++ [Q.length] ++
    Q.flatMap (fun q => (List.ofFn q).flatMap intParts))

/-- A point of `ℤ^{D'}` from `2D'` naturals `(z⁺, z⁻)`. -/
def decodeIntPoint (D' : ℕ) (l : List ℕ) : Fin D' → ℤ :=
  fun i => (l.getD (2 * i) 0 : ℤ) - (l.getD (2 * i + 1) 0 : ℤ)

/-- The path encoded by an answer: consecutive chunks of `2D'` naturals. -/
def decodeIntPath (D' : ℕ) (out : List Bool) : List (Fin D' → ℤ) :=
  (chunks (2 * D') (decodeNats out)).map (decodeIntPoint D')

/-- `x` lies in the box with lower corner `a` and sides `s`. -/
def InBox {D' : ℕ} (a : Fin D' → ℤ) (s : Fin D' → ℕ) (x : Fin D' → ℤ) : Prop :=
  ∀ i, a i ≤ x i ∧ x i < a i + s i

/-- `ℓ1` distance in `ℤ^{D'}`. -/
def intL1 {D' : ℕ} (x y : Fin D' → ℤ) : ℕ := ∑ i, (x i - y i).natAbs

end MovementSorting.Exponent


