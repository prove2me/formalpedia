-- Prove2me | Definitions.Def_NoisyOWMPC_fig6
-- name    : NoisyOWMPC_fig6
-- status  : Definition
-- author  : @iris
-- created : 2026-11-08T07:50:13.636488+00:00
-- url     : https://prove2.me/theorems/05e7751b-76b5-474c-b993-63683319ac64
-- title:
--   The evaluation program of Fig. 6
-- statement:
--   The program $P[x,(\Omega_i)_i,(\Theta_{ijv})_{i,j,v},(K_{ij})_{i,j},(\pi_i)_i]$ answers a query $(i,y_{\mathrm{acc}},w)$ of receiver $i$:
--   1. parse the query and reject malformed inputs;
--   2. reject if $k>1$ and $A_{\Omega_i}(y_{\mathrm{acc}})=0$;
--   3. for every $j\in[r_i]$ compute $U_{ij}(w)=\{v\in[N]:Q_{\Theta_{ijv}}(w_{ijv})=1\}$, and reject if some $j$ has $\mathrm{Guard}_{\mathrm{sel}}(U_{ij}(w))=0$;
--   4. return the validity-tagged encoding of $f_i\bigl(x;\pi_i\oplus(b_{K_{ij}}(U_{ij}(w)))_{j\in[r_i]}\bigr)$.
--
--   Queries and outputs use fixed-length encodings; the all-zero output is rejection. A **program generator** is a deterministic polynomial-time map from $(1^\lambda,x,\text{constants})$ to a circuit computing this function on every input of the fixed length.
--
--   **Formalization Note** The paper fixes no circuit for Fig. 6, so circuits are produced by an arbitrary generator with this specification.
-- source:
--   Ishai, Lu, Zafar, Non-Interactive Cryptography over Noisy Channels from Indistinguishability Obfuscation, STOC 2027 submission (manuscript sha256 3a9569fa…), Construction 5.23 and Fig. 6, pp.30–31

import Mathlib
import Definitions.Def_NoisyOWMPC_Halves
import Definitions.Def_NoisyOWMPC_Functionality
import Definitions.Def_NoisyOWMPC_symEnc
import Definitions.Def_LaconicBarrier_MCircuit
import Definitions.Def_LaconicBarrier_PolyTimeOn

namespace NoisyOWMPC

open KarpLiptonOM LaconicBarrier

variable {k : ℕ} {X : Type} {Y : Fin k → Type} [∀ i, Fintype (Y i)]

/-- The index set `I = {(i, j) : i ∈ [k], j ∈ [r_i]}` of release blocks (Ishai, Lu, Zafar, STOC 2027
submission (manuscript sha256 3a9569fa…), Construction 5.23, p.30). -/
abbrev Blocks (F : Functionality k) (lam : ℕ) : Type := (i : Fin k) × Fin (F.r i lam)

/-- The sampled constants of the program `P` other than `x` (Fig. 6, p.31: "access states
`(Ω_i)_i` …, release states `(Θ_{ijv})_{i,j,v}`, selector keys `(K_{ij})_{i,j}`, and masks
`(π_i)_i`"); the mask `π_i ∈ {0,1}^{r_i}` is stored as its bits `π_{ij}`. -/
abbrev Consts (H : Halves k X Y) (F : Functionality k) (lam : ℕ) : Type :=
  (∀ i, (H.acc i).Sec lam) × (∀ b : Blocks F lam, Fin (H.N lam) → (H.rel b.1).Sec lam) ×
    (∀ _ : Blocks F lam, H.sel.Key lam) × (∀ _ : Blocks F lam, Bool)

/-- A query of receiver `i` to the program (Fig. 6, p.31: "A query `(i, y_acc, w)` containing
receiver `i`'s access observation `y_acc` and release observations `w = (w_{ijv})_{j,v}`"). -/
abbrev Query (H : Halves k X Y) (F : Functionality k) (lam : ℕ) (i : Fin k) : Type :=
  (Fin (H.nacc lam) → Y i) × (Fin (F.r i lam) → Fin (H.N lam) → Fin (H.nrel lam) → Y i)

/-- The accepting set `U_{ij}(w) = {v ∈ [N] : Q_{Θ_{ijv}}(w_{ijv}) = 1}` (Fig. 6, step 3, p.31). -/
noncomputable def acceptSet (H : Halves k X Y) (F : Functionality k) (lam : ℕ) (c : Consts H F lam)
    (i : Fin k) (w : Fin (F.r i lam) → Fin (H.N lam) → Fin (H.nrel lam) → Y i)
    (j : Fin (F.r i lam)) : Finset (Fin (H.N lam)) := by
  classical
  exact Finset.univ.filter fun v => (H.rel i).test lam (c.2.1 ⟨i, j⟩ v) (w j v) = true

open Classical in
/-- **The evaluation program for one-way MPC**, as a function on parsed queries (Fig. 6, p.31):
reject if `k > 1` and `A_{Ω_i}(y_acc) = 0`; reject if some `j` has `Guard_sel(U_{ij}(w)) = 0`;
otherwise return `f_i(x; π_i ⊕ (b_{K_{ij}}(U_{ij}(w)))_{j ∈ [r_i]})`. `none` is rejection. -/
noncomputable def fig6 (H : Halves k X Y) (F : Functionality k) (lam : ℕ)
    (x : Fin (F.lx lam) → Bool) (c : Consts H F lam) (i : Fin k) (q : Query H F lam i) :
    Option (Fin (F.lo i lam) → Bool) :=
  if 1 < k ∧ (H.acc i).test lam (c.1 i) q.1 = false then none
  else if ∃ j, H.sel.guard lam (acceptSet H F lam c i q.2 j) = false then none
  else some (F.f lam i x (fun j =>
    xor (c.2.2.2 ⟨i, j⟩) (H.sel.coin lam (c.2.2.1 ⟨i, j⟩) (acceptSet H F lam c i q.2 j))))

/-- The width `⌈log₂(k + 1)⌉` of the receiver index. -/
def idxW (k : ℕ) : ℕ := Nat.size k

/-- The common symbol width for the output alphabets `Y_i`. -/
def symWY (Y : Fin k → Type) [∀ i, Fintype (Y i)] : ℕ := Finset.univ.sup fun i => symWidth (Y i)

/-- `max_i r_i(λ)`. -/
def rmax (F : Functionality k) (lam : ℕ) : ℕ := Finset.univ.sup fun i => F.r i lam

/-- `max_i ℓ_i(λ)`. -/
def lomax (F : Functionality k) (lam : ℕ) : ℕ := Finset.univ.sup fun i => F.lo i lam

/-- The fixed input length of the program: index field plus the longest query of any receiver. -/
def inLen (H : Halves k X Y) (F : Functionality k) (lam : ℕ) : ℕ :=
  idxW k + symWY Y * (H.nacc lam + rmax F lam * H.N lam * H.nrel lam)

/-- The fixed output length of the program: validity bit, receiver index, longest output. -/
def outLen (F : Functionality k) (lam : ℕ) : ℕ := 1 + idxW k + lomax F lam

/-- The **fixed-length encoding of a query** `(i, y_acc, w)` (Fig. 6, p.31: "Queries and outputs use
fixed-length encodings"): the index `i` in `idxW k` bits, the symbols of `y_acc`, then those of
`w_{ijv}` in the order `(j, v, s)`, then zeros up to `inLen`. -/
noncomputable def queryEnc (H : Halves k X Y) (F : Functionality k) (lam : ℕ) (i : Fin k)
    (q : Query H F lam i) : List Bool :=
  let body := binW (idxW k) i.val ++ (List.ofFn fun s => symEnc (Y i) (symWY Y) (q.1 s)).flatten ++
    (List.ofFn fun j => (List.ofFn fun v =>
      (List.ofFn fun s => symEnc (Y i) (symWY Y) (q.2 j v s)).flatten).flatten).flatten
  body ++ List.replicate (inLen H F lam - body.length) false

/-- The **validity-tagged output encoding** (Fig. 6, p.31: "with a validity bit and receiver index on
outputs; the all-zero output denotes rejection"): `1`, the index `i`, the output `v`, zeros up to
`outLen`. -/
def outEnc (F : Functionality k) (lam : ℕ) (i : Fin k) (v : Fin (F.lo i lam) → Bool) : List Bool :=
  true :: binW (idxW k) i.val ++ bits v ++ List.replicate (lomax F lam - F.lo i lam) false

open Classical in
/-- The **bit-level function of Fig. 6** on inputs of length `inLen` (Fig. 6, step 1, p.31: "Parse
`(i, y_acc, w)` and reject malformed inputs"): the encoding of the program's answer on a string that
encodes a query, and the all-zero output on every other string. -/
noncomputable def fig6Bits (H : Halves k X Y) (F : Functionality k) (lam : ℕ)
    (x : Fin (F.lx lam) → Bool) (c : Consts H F lam) (u : List Bool) : List Bool :=
  if h : ∃ q : (i : Fin k) × Query H F lam i, queryEnc H F lam q.1 q.2 = u then
    match fig6 H F lam x c h.choose.1 h.choose.2 with
    | none => List.replicate (outLen F lam) false
    | some v => outEnc F lam h.choose.1 v
  else List.replicate (outLen F lam) false

/-- The release blocks `(i, j)` in lexicographic order. -/
def blockList (F : Functionality k) (lam : ℕ) : List (Blocks F lam) :=
  (List.finRange k).flatMap fun i => List.ofFn fun j : Fin (F.r i lam) => (⟨i, j⟩ : Blocks F lam)

/-- The encoding of the program constants other than `x`: the access states, the release states in
the order `(i, j, v)`, the selector keys and the mask bits. -/
def constsEnc (H : Halves k X Y) (F : Functionality k) (lam : ℕ) (c : Consts H F lam) :
    List Bool :=
  QAdvFew.PoQOracle.tup [QAdvFew.PoQOracle.tup (List.ofFn fun i => (H.acc i).enc lam (c.1 i)),
    QAdvFew.PoQOracle.tup ((blockList F lam).flatMap fun b =>
      List.ofFn fun v => (H.rel b.1).enc lam (c.2.1 b v)),
    QAdvFew.PoQOracle.tup ((blockList F lam).map fun b => H.sel.enc lam (c.2.2.1 b)),
    (blockList F lam).map fun b => c.2.2.2 b]

/-- A **program generator**: from `λ`, `x` and the sampled constants it outputs a circuit `P` with
`inLen` inputs. -/
abbrev ProgGen (H : Halves k X Y) (F : Functionality k) : Type :=
  (lam : ℕ) → (Fin (F.lx lam) → Bool) → Consts H F lam → MCircuit (inLen H F lam)

/-- `gen` is a **deterministic polynomial-time generator of Fig. 6's program** (Construction 5.23,
step 3, p.30: "Construct the program `P` in Fig. 6 from `x` and the sampled states, selector keys,
and masks"): one machine computes the description of `gen λ x c` from `(1^λ, x, c)` in polynomial
time, and the circuit computes `fig6Bits` on every input of length `inLen`.

**Formalization Note** The paper fixes no circuit for Fig. 6; the construction is stated for every
such generator (paper's implementation is one). -/
def IsFig6Gen (H : Halves k X Y) (F : Functionality k) (gen : ProgGen H F) : Prop :=
  PolyTimeOn (ι := (lam : ℕ) × (Fin (F.lx lam) → Bool) × Consts H F lam)
    (fun z => [unary z.1, bits z.2.1, constsEnc H F z.1 z.2.2]) (fun z => (gen z.1 z.2.1 z.2.2).code) ∧
  ∀ lam x c (u : List Bool), u.length = inLen H F lam → (gen lam x c).eval u = fig6Bits H F lam x c u

end NoisyOWMPC


