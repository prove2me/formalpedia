-- Prove2me | Definitions.Def_QuadSDE_Supplement_Succinct
-- name    : QuadSDE_Supplement_Succinct
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T01:12:48.525571+00:00
-- url     : https://prove2.me/theorems/062da594-3f61-4428-9733-4091c7800b93
-- title:
--   Succinct input model of APX-ODE / APX-SDE, the circuits DriftRow, InitSign, InitPrefix, and dyadic rationals with $b$ bits
-- statement:
--   An instance of **APX-ODE in the succinct input model** consists of the dimension $N$, the drift parameters $s$ (sparsity), $r$ (channels), $J$ (strength), the final time $T$, a bit length $v_b$, an observable $u_0$ ($x_i$ or $x_ix_j$), and three classical Boolean circuits whose input is a row index $i\in[N]$ written in binary on $\lceil\log_2(N+1)\rceil$ wires:
--   1. **DriftRow** outputs $s$ slots; each slot is either blank or holds positions $(j,k)$ and a value;
--   2. **InitSign** outputs the sign of $Y_i$;
--   3. **InitPrefix** outputs the prefix sum $\sum_{j\le i}Y_j^2$ (Eq. (17)).
--
--   Values are written exactly as $\pm\,\text{numerator}/2^{\text{exponent}}$ with $v_b$-bit numerator and exponent. An instance of **APX-SDE** adds the noise rates $p,q$. The circuits **specify** $(c,Y)$ when they are well formed, every non-blank slot of row $i$ lists a nonzero $c_{ijk}$ with its exact value, every nonzero $c_{ijk}$ appears in exactly one slot, InitSign outputs $1$ exactly when $Y_i<0$, and InitPrefix outputs exactly $\sum_{j\le i}Y_j^2$; the drift is **valid** when it is admissible (symmetric, norm and volume preserving) with strength $\le J$, sparsity $\le s$ and at most $r$ channels. Scalars are admissible when $J>0$, $r,s\ge1$, $T\ge0$ (and $0<p,q\le1$). A real number is a **dyadic rational with $b$ bits** if it equals $i/2^e$ with integers $|i|\le2^b$ and $0\le e\le b$ (footnote 4). The instance, and a majority instance, are written as bit strings in self-delimiting binary; $\sum_xF(x)$ counts the inputs accepted by a one-output circuit.
--
--   These are the outputs of the reductions of Theorems 5 and 6.
--
--   **Formalization Note** Circuits are `QAlgorithms.BoolCircuit` (AND/OR/NOT, fan-in 2); the source fixes no basis. Index $i$ (0-based in Lean) is fed to the circuits as the source's 1-based value $i+1$, most significant bit first. $J$, $T$, $p$, $q$ are rationals (binary numbers are dyadic rationals). The error tolerance is not part of the record; Theorems 5 and 6 say which tolerances suffice. The pair $(c,Y)$ is determined by the circuits.
-- source:
--   Bravyi, Byrne, Zayats, Zhuk, Zlokapa, Quantum algorithms for stochastic nonlinear differential equations, arXiv:2606.08349 (sha256 29bd9b01…94cdf), Problems 1–2 p. 2; §3 p. 13; §3.1 p. 14; footnote 4 p. 39; §6 p. 39; §6.5 p. 46

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Basic
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_QAlgorithms_ClassicalBinaryEncoding
import Definitions.Def_QAlgorithms_ClassicalRationalEncoding
import Definitions.Def_QuadSDE_DriftClass
import Definitions.Def_QuadSDE_Observable
import Definitions.Def_QuadSDE_Instance

open QAlgorithms QAlgorithms.Complexity QAlgorithms.LocalHamiltonian

noncomputable section

namespace QuadSDE.Supplement

/-- Bravyi, Byrne, Zayats, Zhuk, Zlokapa, *Quantum algorithms for stochastic nonlinear differential
equations*, arXiv:2606.08349 (sha256 29bd9b01…), §3.1, p. 14: the number of input wires of the
succinct-model circuits, `⌈log₂(N + 1)⌉`, enough to write a row index `i ∈ [N]` in binary. -/
def idxWidth (N : ℕ) : ℕ := Nat.clog 2 (N + 1)

/-- The input of a succinct-model circuit for the index `i : Fin N`: the paper's 1-based index
`i + 1` in binary on `⌈log₂(N + 1)⌉` wires, most significant bit first (`QAlgorithms.natToBits`). -/
def idxBits {N : ℕ} (i : Fin N) : Fin (idxWidth N) → Bool :=
  natToBits (idxWidth N) (i.val + 1)

/-- The value of a bit list read in binary, most significant bit first. -/
def bitsVal (l : List Bool) : ℕ :=
  l.foldl (fun acc b => 2 * acc + if b then 1 else 0) 0

/-- p. 14 ("with the binary representation of real numbers") and footnote 4, p. 39: the fixed exact
binary format of a value with `vb` bits: a sign bit (`true` = negative), a numerator of `vb` bits,
an exponent of `vb` bits, both most significant bit first; the value is `± numerator / 2^exponent`.
Its width is `1 + 2 vb`. -/
def valWidth (vb : ℕ) : ℕ := 1 + 2 * vb

/-- Decoding of the value format of `valWidth vb` bits (see `valWidth`). -/
def decodeDyadic (vb : ℕ) (l : List Bool) : ℚ :=
  (if l.getD 0 false then -1 else 1) * (bitsVal ((l.drop 1).take vb) : ℚ) /
    2 ^ bitsVal ((l.drop (1 + vb)).take vb)

/-- The width of one slot of the `DriftRow` output: a blank flag (`true` = blank symbol), the
positions `j, k` (each as its 1-based value in `⌈log₂(N + 1)⌉` bits), and the value. -/
def slotWidth (N vb : ℕ) : ℕ := 1 + 2 * idxWidth N + valWidth vb

/-- The `a`-th slot (`a < s`) of a `DriftRow` output word. -/
def slot (N vb : ℕ) (out : List Bool) (a : ℕ) : List Bool :=
  (out.drop (a * slotWidth N vb)).take (slotWidth N vb)

/-- The slot is the blank symbol. -/
def slotBlank (sl : List Bool) : Prop := sl.getD 0 false = true

/-- The 1-based position `j` written in a slot. -/
def slotJ (N : ℕ) (sl : List Bool) : ℕ := bitsVal ((sl.drop 1).take (idxWidth N))

/-- The 1-based position `k` written in a slot. -/
def slotK (N : ℕ) (sl : List Bool) : ℕ := bitsVal ((sl.drop (1 + idxWidth N)).take (idxWidth N))

/-- The value written in a slot. -/
def slotVal (N vb : ℕ) (sl : List Bool) : ℚ := decodeDyadic vb (sl.drop (1 + 2 * idxWidth N))

/-- §3.1, p. 14, and Problem 1, p. 2: an instance of APX-ODE in the succinct input model. It holds
the dimension `N`, the drift parameters `s` (sparsity), `r` (channels), `J` (strength), the final
time `T`, the bit length `vb` of the value format, the observable `u₀`, and three classical Boolean
circuits:
* `driftRow` takes a row index `i ∈ [N]` and outputs `s` slots listing the positions `(j, k)` and
  values of the nonzero entries of row `i` of `c`, padded with the blank symbol;
* `initSign` takes `i` and outputs the sign of `Y_i`;
* `initPrefix` takes `i` and outputs the prefix sum `Σ_{j ≤ i} Y_j²` (Eq. (17)).

**Formalization Note.** p. 13: "The dimension `N`, drift parameters `s, r, J` … final time `T` …
are supplied explicitly in binary"; `J, T` are rationals (a binary number is a dyadic rational).
The error tolerance is not part of the record: Theorems 5 and 6 state which tolerances suffice.
The circuits are `QAlgorithms.BoolCircuit` (AND/OR/NOT, fan-in 2); their input and output formats are
fixed by `idxBits`, `slot`, `valWidth`. -/
structure SuccinctODE where
  N : ℕ
  s : ℕ
  r : ℕ
  J : ℚ
  T : ℚ
  vb : ℕ
  obs : Observable N
  driftRow : BoolCircuit (idxWidth N) (s * slotWidth N vb)
  initSign : BoolCircuit (idxWidth N) 1
  initPrefix : BoolCircuit (idxWidth N) (valWidth vb)

/-- Problem 2, p. 2: an instance of APX-SDE in the succinct input model: an APX-ODE record together
with the noise rates `p, q`. -/
structure SuccinctSDE extends SuccinctODE where
  p : ℚ
  q : ℚ

/-- p. 13 ("We assume `J, r, s > 0`") and Problem 1: the scalar parameters are admissible,
`J > 0`, `r ≥ 1`, `s ≥ 1`, `T ≥ 0`. -/
def SuccinctODE.ParamsValid (x : SuccinctODE) : Prop :=
  0 < x.J ∧ 1 ≤ x.r ∧ 1 ≤ x.s ∧ 0 ≤ x.T

/-- Problem 2: the noise rates are admissible, `0 < p, q ≤ 1`, on top of `ParamsValid`. -/
def SuccinctSDE.ParamsValid (x : SuccinctSDE) : Prop :=
  x.toSuccinctODE.ParamsValid ∧ 0 < x.p ∧ x.p ≤ 1 ∧ 0 < x.q ∧ x.q ≤ 1

/-- §3.1, p. 14: the circuits of the instance specify the drift tensor `c` and the noise-free
initial condition `Y`:
1. the three circuits are well formed;
2. for every row `i`, every non-blank slot of `driftRow(i)` holds 1-based positions of some
   `(j, k)` with `c_{ijk} ≠ 0` and the exact value `c_{ijk}`, and every nonzero `c_{ijk}` of row `i`
   appears in exactly one non-blank slot ("contain each nonzero ordered pair exactly once", p. 46);
3. `initSign(i)` outputs `1` exactly when `Y_i < 0`;
4. `initPrefix(i)` outputs exactly `Σ_{j ≤ i} Y_j²`.

The pair `(c, Y)` is determined by the circuits. -/
def SuccinctODE.Specifies (x : SuccinctODE) (c : Coeff x.N) (Y : Fin x.N → ℝ) : Prop :=
  x.driftRow.WellFormed ∧ x.initSign.WellFormed ∧ x.initPrefix.WellFormed ∧
  (∀ i : Fin x.N,
    let out := List.ofFn (x.driftRow.eval (idxBits i))
    (∀ a : Fin x.s, ¬ slotBlank (slot x.N x.vb out a) →
      ∃ j k : Fin x.N, slotJ x.N (slot x.N x.vb out a) = j.val + 1 ∧
        slotK x.N (slot x.N x.vb out a) = k.val + 1 ∧
        c i j k = (slotVal x.N x.vb (slot x.N x.vb out a) : ℝ) ∧ c i j k ≠ 0) ∧
    (∀ j k : Fin x.N, c i j k ≠ 0 →
      ∃! a : Fin x.s, ¬ slotBlank (slot x.N x.vb out a) ∧
        slotJ x.N (slot x.N x.vb out a) = j.val + 1 ∧
        slotK x.N (slot x.N x.vb out a) = k.val + 1)) ∧
  (∀ i : Fin x.N, x.initSign.eval (idxBits i) 0 = true ↔ Y i < 0) ∧
  (∀ i : Fin x.N,
    ((decodeDyadic x.vb (List.ofFn (x.initPrefix.eval (idxBits i))) : ℚ) : ℝ) =
      ∑ j ∈ Finset.univ.filter (fun j : Fin x.N => j ≤ i), Y j ^ 2)

/-- §1, pp. 3–4: the specified drift belongs to the class `𝒟` with the instance's parameters:
admissible (symmetric, norm and volume preserving), strength `≤ J`, sparsity `≤ s`, at most `r`
channels. -/
def SuccinctODE.DriftValid (x : SuccinctODE) (c : Coeff x.N) : Prop :=
  IsAdmissibleDrift c ∧ strengthLE c x.J ∧ sparsityLE c x.s ∧ channelsLE c x.r

/-- Footnote 4, p. 39: a real number is a dyadic rational with `b` bits if it equals `i / 2^e` for
integers `i, e` with `|i| ≤ 2^b` and `0 ≤ e ≤ b`. -/
def IsDyadicBits (v : ℝ) (b : ℕ) : Prop :=
  ∃ (i : ℤ) (e : ℕ), |i| ≤ 2 ^ b ∧ e ≤ b ∧ v = (i : ℝ) / 2 ^ e

/-- The binary code of a Boolean gate: a two-bit tag for AND/OR/NOT, then the two input wires in
self-delimiting binary. -/
def encodeBoolGate (g : BoolGate) : Str :=
  (match g.op with
    | .and => [false, false]
    | .or => [false, true]
    | .not => [true, false]) ++ encBin g.a ++ encBin g.b

/-- The binary code of a Boolean circuit: the number of gates, the gate codes, then the output
wires, all in self-delimiting binary. -/
def encodeBoolCircuit {n m : ℕ} (C : BoolCircuit n m) : Str :=
  encBin C.gates.length ++ C.gates.flatMap encodeBoolGate ++ (List.ofFn C.outputs).flatMap encBin

/-- The output string of an APX-ODE instance: `N, s, r` in binary, `J, T` as rationals, `vb` in
binary, the observable, then the three circuits. -/
def SuccinctODE.encode (x : SuccinctODE) : Str :=
  encBin x.N ++ encBin x.s ++ encBin x.r ++ encRat x.J ++ encRat x.T ++ encBin x.vb ++
    QuadSDE.encodeObservable x.obs ++ encodeBoolCircuit x.driftRow ++
    encodeBoolCircuit x.initSign ++ encodeBoolCircuit x.initPrefix

/-- The output string of an APX-SDE instance: the APX-ODE part, then `p, q` as rationals. -/
def SuccinctSDE.encode (x : SuccinctSDE) : Str :=
  x.toSuccinctODE.encode ++ encRat x.p ++ encRat x.q

/-- §6, p. 39: the number `Σ_x F(x)` of inputs accepted by the Boolean function
`F : {0,1}ⁿ → {0,1}` computed by a classical circuit with one output (the majority problem asks
whether it exceeds `2^{n−1}`). -/
def acceptCount {n : ℕ} (F : BoolCircuit n 1) : ℕ :=
  (Finset.univ.filter fun x : Fin n → Bool => F.eval x 0 = true).card

end QuadSDE.Supplement


