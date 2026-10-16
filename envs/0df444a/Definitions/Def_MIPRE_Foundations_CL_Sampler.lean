-- Prove2me | Definitions.Def_MIPRE_Foundations_CL_Sampler
-- name    : MIPRE_Foundations_CL_Sampler
-- status  : Definition
-- author  : @thomasvidick
-- created : 2026-10-15T18:05:38.211433+00:00
-- url     : https://prove2.me/theorems/58e35120-9600-4b76-8b11-35de649101f8
-- title:
--   Samplers: programs presenting two conditionally linear functions over $\mathbb{F}_2$ through the query interface
-- statement:
--   A sampler, the question half of a normal form verifier, is a program of the ambient cost model which on index $n$ presents two $\ell$-level conditionally linear functions $L^{\mathsf A}, L^{\mathsf B}$ on $\mathbb{F}_2^{s(n)}$ through a fixed query interface.
--
--   **Players, field, bit strings.** `MIPRE.Player` is `alice | bob`, with `Player.toBool` (Alice `false`), `Player.ofBool` and a `SizedEncoding`; `MIPRE.CL.𝔽₂` is `ZMod 2`; `toBits v` lists the coordinates of $v$, `ofBits s l` reads a vector off a bit string (missing bits $0$, extra ignored), `indicatorBits S` is the indicator string of a set of coordinates.
--
--   **Queries.** `Sampler.Query` has constructors `dimension`, `marginal w j z`, `linear w j u y`, `factor w j u` ($w$ a player, $j$ a level, $z, u, y$ bit strings); `Query.toTuple` is the tuple $(\mathit{kind}, w, j, u, y)$, missing arguments empty, `Query.ofTuple` reads it back, `Query.instSizedEncoding` encodes via the tuple.
--
--   **Samplers.** `MIPRE.CL.Sampler ℓ` has fields `prog : Prog`, `closed : prog.WellScoped 1`, `dim : ℕ → ℕ` ($s(n)$), `cl n w : CLFun 𝔽₂ (Fin (dim n)) ℓ`, `cl_exactlyOn` (`ExactlyOn Finset.univ`), the run clauses `runs_dimension`, `runs_marginal`, `runs_linear`, `runs_factor` (`prog` on $\mathrm{encode}(n, q)$ runs, `Prog.Runs`, to the encoded $s(n)$; $L^{w}_{\le j}\,z$ via `truncate j`; $L^{w}_{j,u}\,y$ via `mapOfPrefix (j-1)`; the indicator of $V^{w}_{j,u}$ via `factorOfPrefix (j-1)`; for $1 \le j \le \ell$, $z, y$ of length $s(n)$, $u$ in the image of $L^{w}_{< j}$), and `halts` (`prog` halts on $\mathtt{cons}(\mathrm{encode}\,n, d)$ for every $n$, $d$). `Sampler.TimeBoundAt S n T k` is
--   $$\forall d : \mathrm{Data},\quad \mathrm{HaltsWithin}\bigl(S.\mathrm{prog},\ \mathtt{cons}(\mathrm{encode}\,n, d),\ T\,(\mathrm{size}(d)+1)^{k}\bigr);$$
--   `Sampler.size S` $= \mathrm{esize}(S.\mathrm{prog})$; `Sampler.dist S n` is the `clDist` of the two CL functions.
--
--   The embedded lemmas are the round trips for players, queries and vectors (and the private `ite_decide_eq_one`), the lengths of `toBits` and `indicatorBits`, `TimeBoundAt.mono`, `dist_nonneg` and `sum_dist`.
--
--   **Formalization Note**. The field size is fixed at $2$ (`def:sampler`). The correctness clauses are imposed exactly where the paper imposes them, and `prog` must halt on every input $(n, d)$, well formed or not; `TimeBoundAt` is the paper's supremum of running times at index $n$, read as a polynomial bound in the input size (the model has no cursor into its input).
-- source:
--   https://github.com/vidick/MIPRE-formalization/blob/70cbf1c52e3d5e1dff1162fdf952c9a9f4bd99ed/MIPRE/Foundations/CL/Sampler.lean; blueprint def:sampler; companion paper (vidick/MIPRE-proof), linear.tex, Definition def:sampler and def:sampler-sample

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CL/Sampler.lean (definition bundle: declarations the uploaded statements rest on);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime

/-!
# Samplers

Blueprint `def:sampler` (paper `linear.tex`, Definition `def:sampler`; ledger node `1.1.3`
with `def:normal-verifier`). A sampler is the half of a normal form verifier that produces the
questions: a program of the ambient model (`MIPRE.Cost`) that, on an index `n`, presents two
conditionally linear functions `L^𝖠, L^𝖡` on `𝔽₂^{s(n)}` — one per player — through a fixed
*query interface*, so that the question distribution of the game at index `n` is the CL
distribution `(L^𝖠 x, L^𝖡 x)`, `x` uniform. The interface is what every transformation of the
pipeline (introspection, oracularization, answer reduction) is written against, which is why the
blueprint fixes it once and for all. It is the paper's, restricted to field size `2` as the
blueprint's normal form verifiers are:

* `(n, dimension) ↦ s(n)`;
* `(n, w, marginal, j, z) ↦ L^w_{≤ j}(z)`, the `j`-th marginal (`CLFun.truncate`);
* `(n, w, linear, j, u, y) ↦ L^w_{j,u}(y)`, the `j`-th linear map with prefix `u`
  (`CLFun.mapOfPrefix`);
* `(n, w, factor, j, u) ↦ V^w_{j,u}`, the `j`-th factor space with prefix `u`, as an indicator
  vector (`CLFun.factorOfPrefix`),

for `1 ≤ j ≤ ℓ`, `z, y` of length `s(n)`, and — for the last two — `u` in the image of
`L^w_{< j}`, exactly as the paper quantifies (`CLFun.SupportedOn.factorOfPrefix_eval` is what
makes the answers well defined there). The sampler must moreover halt on *every* input of the
form `(n, …)`; the paper's bounded format checks are what make its running time on index `n`,
the supremum over all such inputs, finite. `Sampler.TimeBoundAt n T k` is that supremum
bounded by `T`, read as halting within cost `T · (|d| + 1)^k` on every input `(n, d)`: the
ambient model has no cursor into its input, and a bound uniform over all inputs is not
satisfiable by any program that walks a list of unbounded length (see the module docstring of
`MIPRE.Foundations.Verifier`, which also says why the degree `k` is needed).
Vectors and register subspaces of `𝔽₂^s` travel as bit strings of length `s` (`toBits`,
`ofBits`, `indicatorBits`); the paper's binary representation over `𝔽_{2^k}` through a
self-dual basis is not needed at field size `2`.

The CL functions of a sampler are required to be *exactly* on the whole space
(`CLFun.ExactlyOn`): their factor spaces partition the coordinates, item (2) of `lem:cl-kth`,
which the paper's definition demands of them.

## Conventions

The input of the program is the one value `encode (n, q)` for `q : Sampler.Query`, with a query
encoded as the tuple `(kind, w, j, u, y)`, missing arguments empty (`Sampler.Query.toTuple`).
Players are `MIPRE.Player`, Alice first.
-/

namespace MIPRE

/-- The two players of a nonlocal game. -/
inductive Player
  /-- The first player. -/
  | alice
  /-- The second player. -/
  | bob
  deriving DecidableEq

namespace Player

/-- Players as bits: Alice is `false`, Bob is `true`. -/
def toBool : Player → Bool
  | alice => false
  | bob => true

/-- The player of a bit. -/
def ofBool : Bool → Player
  | false => alice
  | true => bob

@[simp] theorem ofBool_toBool (w : Player) : ofBool (toBool w) = w := by cases w <;> rfl

instance : Cost.SizedEncoding Player where
  encode w := Cost.encode w.toBool
  decode d := (Cost.decode d : Option Bool).map ofBool
  decode_encode w := by simp [Cost.SizedEncoding.decode_encode]

end Player

namespace CL

open Cost

/-- The binary field `𝔽₂`: the field size of every sampler of a normal form verifier (blueprint
`def:sampler`). -/
abbrev 𝔽₂ : Type := ZMod 2

/-! ## Vectors of `𝔽₂^s` as bit strings -/

/-- The bit string of a vector in `𝔽₂^s`: its list of coordinates. -/
def toBits {s : ℕ} (v : Fin s → 𝔽₂) : BitStr := List.ofFn fun i => decide (v i = 1)

/-- The vector in `𝔽₂^s` read off a bit string; missing bits read as `0`, bits beyond `s` are
ignored. -/
def ofBits (s : ℕ) (l : BitStr) : Fin s → 𝔽₂ := fun i => if l.getD i false then 1 else 0

/-- The indicator bit string of a set of coordinates: the paper's representation of a register
subspace of `𝔽₂^s` as a vector in `{0,1}^s`. -/
def indicatorBits {s : ℕ} (S : Finset (Fin s)) : BitStr := List.ofFn fun i => decide (i ∈ S)

@[simp] theorem length_toBits {s : ℕ} (v : Fin s → 𝔽₂) : (toBits v).length = s :=
  List.length_ofFn

@[simp] theorem length_indicatorBits {s : ℕ} (S : Finset (Fin s)) :
    (indicatorBits S).length = s :=
  List.length_ofFn

theorem ite_decide_eq_one (a : 𝔽₂) : (if decide (a = 1) then (1 : 𝔽₂) else 0) = a := by
  revert a
  decide

@[simp] theorem ofBits_toBits {s : ℕ} (v : Fin s → 𝔽₂) : ofBits s (toBits v) = v := by
  funext i
  simp only [ofBits, toBits, List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, dite_true,
    Option.getD_some, Fin.eta]
  exact ite_decide_eq_one (v i)

theorem toBits_ofBits {s : ℕ} {l : BitStr} (hl : l.length = s) : toBits (ofBits s l) = l := by
  refine List.ext_getElem (by simp [hl]) fun i hi hi' => ?_
  simp only [toBits, List.getElem_ofFn, ofBits, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi', Option.getD_some]
  cases l[i] <;> decide

/-! ## The query interface -/

/-- The queries a sampler answers (`def:sampler`): the paper's `6`-input Turing machine, whose
inputs after the index `n` are a player label `w`, a query kind, a level `j` and up to two
vectors. -/
inductive Sampler.Query
  /-- `(n, dimension)`: the dimension `s(n)`. -/
  | dimension
  /-- `(n, w, marginal, j, z)`: the `j`-th marginal `L^w_{≤ j}(z)`. -/
  | marginal (w : Player) (j : ℕ) (z : BitStr)
  /-- `(n, w, linear, j, u, y)`: the `j`-th linear map with prefix `u`, applied to `y`. -/
  | linear (w : Player) (j : ℕ) (u y : BitStr)
  /-- `(n, w, factor, j, u)`: the `j`-th factor space with prefix `u`, as an indicator vector. -/
  | factor (w : Player) (j : ℕ) (u : BitStr)
  deriving DecidableEq

namespace Sampler.Query

/-- A query as the tuple `(kind, w, j, u, y)`, missing arguments empty. -/
def toTuple : Query → ℕ × Player × ℕ × BitStr × BitStr
  | dimension => (0, .alice, 0, [], [])
  | marginal w j z => (1, w, j, z, [])
  | linear w j u y => (2, w, j, u, y)
  | factor w j u => (3, w, j, u, [])

/-- Reading a query back from its tuple. -/
def ofTuple : ℕ × Player × ℕ × BitStr × BitStr → Option Query
  | (0, _, _, _, _) => some dimension
  | (1, w, j, z, _) => some (marginal w j z)
  | (2, w, j, u, y) => some (linear w j u y)
  | (3, w, j, u, _) => some (factor w j u)
  | _ => none

@[simp] theorem ofTuple_toTuple (q : Query) : ofTuple q.toTuple = some q := by
  cases q <;> rfl

/-- Queries are data: their tuple, encoded. -/
instance : SizedEncoding Query where
  encode q := encode q.toTuple
  decode d := (decode d : Option (ℕ × Player × ℕ × BitStr × BitStr)).bind ofTuple
  decode_encode q := by simp [SizedEncoding.decode_encode]

end Sampler.Query

/-- Blueprint `def:sampler`: an `ℓ`-level sampler (field size `2`). A program of the ambient
model which, on index `n`, presents an `ℓ`-level CL function on `𝔽₂^{s(n)}` for each player
through the query interface — dimension, marginals, stage maps and factor spaces (the data of
`lem:cl-kth`) — and halts on every input of the form `(n, …)`. The correctness clauses are
imposed exactly where the paper imposes them: well-formed vectors, levels `1 ≤ j ≤ ℓ`, and
prefixes `u` in the image of `L^w_{< j}`. -/
structure Sampler (ℓ : ℕ) where
  /-- The program; its one input is `encode (n, q)` for an index `n` and a query `q`. -/
  prog : Prog
  /-- The program is closed. -/
  closed : prog.WellScoped 1
  /-- The dimension `s(n)` of the ambient space `𝔽₂^{s(n)}` on index `n`. -/
  dim : ℕ → ℕ
  /-- The CL functions of the sampler on index `n`, one per player. -/
  cl : (n : ℕ) → Player → CLFun 𝔽₂ (Fin (dim n)) ℓ
  /-- Each is exactly on the whole space: its factor spaces partition the coordinates
  (item (2) of `lem:cl-kth`). -/
  cl_exactlyOn : ∀ (n : ℕ) (w : Player), (cl n w).ExactlyOn Finset.univ
  /-- `(n, dimension) ↦ s(n)`. -/
  runs_dimension : ∀ (n : ℕ), ∃ t, prog.Runs (encode (n, Sampler.Query.dimension)) (encode (dim n)) t
  /-- `(n, w, marginal, j, z) ↦ L^w_{≤ j}(z)`, for `1 ≤ j ≤ ℓ` and `z` of length `s(n)`. -/
  runs_marginal : ∀ (n : ℕ) (w : Player) (j : ℕ) (z : BitStr), 1 ≤ j → j ≤ ℓ → z.length = dim n →
    ∃ t, prog.Runs (encode (n, Sampler.Query.marginal w j z))
      (encode (toBits (((cl n w).truncate j).eval (ofBits (dim n) z)))) t
  /-- `(n, w, linear, j, u, y) ↦ L^w_{j,u}(y)`, for `1 ≤ j ≤ ℓ`, `u` in the image of
  `L^w_{< j}` and `y` of length `s(n)`. -/
  runs_linear : ∀ (n : ℕ) (w : Player) (j : ℕ) (u y : BitStr), 1 ≤ j → j ≤ ℓ →
    (∃ x, u = toBits (((cl n w).truncate (j - 1)).eval x)) → y.length = dim n →
    ∃ t, prog.Runs (encode (n, Sampler.Query.linear w j u y))
      (encode (toBits ((cl n w).mapOfPrefix (j - 1) (ofBits (dim n) u) (ofBits (dim n) y)))) t
  /-- `(n, w, factor, j, u) ↦ V^w_{j,u}` as an indicator vector, for `1 ≤ j ≤ ℓ` and `u` in the
  image of `L^w_{< j}`. -/
  runs_factor : ∀ (n : ℕ) (w : Player) (j : ℕ) (u : BitStr), 1 ≤ j → j ≤ ℓ →
    (∃ x, u = toBits (((cl n w).truncate (j - 1)).eval x)) →
    ∃ t, prog.Runs (encode (n, Sampler.Query.factor w j u))
      (encode (indicatorBits ((cl n w).factorOfPrefix (j - 1) (ofBits (dim n) u)))) t
  /-- The sampler halts on every input of the form `(n, …)`, well formed or not. -/
  halts : ∀ (n : ℕ) (d : Data), Halts prog (.cons (encode n) d)

namespace Sampler

variable {ℓ : ℕ} (S : Sampler ℓ)

/-- `TIME_𝒮(n) ≤ T`: the sampler halts within cost `T · (|d| + 1)^k` on every input `(n, d)`,
well formed or not — the supremum of `def:sampler` at index `n`, bounded by a polynomial in
the size of the input with coefficient `T` and degree `k`. -/
def TimeBoundAt (n T k : ℕ) : Prop :=
  ∀ d : Data, HaltsWithin S.prog (.cons (encode n) d) (T * (d.size + 1) ^ k)

/-- The bound is monotone in both parameters. -/
theorem TimeBoundAt.mono {ℓ : ℕ} {S : Sampler ℓ} {n T k T' k' : ℕ} (h : S.TimeBoundAt n T k)
    (hT : T ≤ T') (hk : k ≤ k') : S.TimeBoundAt n T' k' := fun d =>
  let ⟨r, t, ht, hrun⟩ := h d
  ⟨r, t, ht.trans (Nat.mul_le_mul hT (Nat.pow_le_pow_right (by omega) hk)), hrun⟩

/-- The description length `|𝒮|` of the sampler. -/
def size : ℕ := esize S.prog

/-! The paper's `s(n) ≤ TIME_𝒮(n)` (a marginal query writes `s(n)` output cells) does not
follow from `TimeBoundAt`, whose bound grows with the input — the query carrying a vector of
length `s(n)` is itself of size about `3 s(n)`. Where the pipeline needs it, it is a clause of
`Verifier.IsBounded`. -/

/-- The distribution of the sampler on index `n` (paper `def:sampler-sample`): the CL
distribution of its two CL functions, `(L^𝖠 x, L^𝖡 x)` for `x` uniform in `𝔽₂^{s(n)}`. -/
noncomputable def dist (n : ℕ) : (Fin (S.dim n) → 𝔽₂) → (Fin (S.dim n) → 𝔽₂) → ℝ :=
  clDist (S.cl n .alice).eval (S.cl n .bob).eval

theorem dist_nonneg (n : ℕ) (a b : Fin (S.dim n) → 𝔽₂) : 0 ≤ S.dist n a b :=
  clDist_nonneg _ _ a b

theorem sum_dist (n : ℕ) : ∑ a, ∑ b, S.dist n a b = 1 :=
  sum_clDist _ _

end Sampler

end CL

end MIPRE


