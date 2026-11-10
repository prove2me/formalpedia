-- Prove2me | Definitions.Def_ObfEF_Incremental_Padding
-- name    : ObfEF_Incremental_Padding
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:57:29.638245+00:00
-- url     : https://prove2.me/theorems/50623513-0f06-469a-820d-0c1eada36ffc
-- title:
--   The block length c_x, the padding topology U_{il,ol,s,K}, the configurations G_Z(C, C') and Pad(C) (Definition 3.9)
-- statement:
--   **Block length.** A straight-line program is a list of instructions of the forms $0$, $1$, $\neg a$, $a\wedge b$, $a\vee b$, whose operands are variables or earlier instructions; it computes a formula $\varphi$ over $\{\to,\bot\}$ if its last instruction has the value of $\varphi$ under every assignment. For constants $c_F$ and $c_x$, $c_x$ is a **block length for $c_F$** if every formula of size at most $c_F$ is computed by the last instruction of a straight-line program of exactly $c_x$ instructions (p. 52; shorter programs are filled with copies $a\wedge a$).
--
--   **Padding (Definition 3.9).** Let $il,ol,s\ge1$ and $K\ge2$ a power of two. $U_{il,ol,s,K}$ is $U_{il,ol,M}$ with
--   $$M=2s+2c_xK+K+ol$$
--   cells, forming in this order: regions $A$ and $B$ of $s$ cells each; an extension block $X_i$ of $c_x$ cells for each $i\in[K]$; a line block $Y_i$ of $c_x$ cells for each $i\in[K]$, whose last cell is $\hat Y_i$; the chain cells $q_K,\dots,q_1$; and the cells $F_1,\dots,F_{ol}$. The chain has the order $\pi$ (a permutation of $[K]$) if $q_t$ has the instruction $\hat Y_{\pi(t)}\wedge q_{t+1}$ for $t<K$ and $q_K$ has $\hat Y_{\pi(K)}\wedge\hat Y_{\pi(K)}$.
--
--   A circuit $C$ over $B$ with noninput vertices $z_1,\dots,z_t$ in canonical topological order is **placed** in cells $j_1<\dots<j_t$ if cell $j_i$ has the instruction of $z_i$ with the outputs of the cells of its in-neighbours, or the input wires, as operands (Definition 3.3). For circuits $C,C'$ with $il$ inputs, $ol$ outputs and size at most $s$, each possibly the symbol $\diamond$, and a region $Z\in\{A,B\}$ whose circuit is not $\diamond$, the configuration $G_Z(C,C')$ places $C$ in the first cells of $A$ and $C'$ in the first cells of $B$, the remaining cells of $A$ and $B$ inactive; the extension blocks are inactive, every $\hat Y_i$ has the instruction $1$, the other line-block cells are inactive; the chain has the identity order; $F_k$ has the instruction $q_1\wedge\iota_Z(u_k)$ for the $k$th output $u_k$ of the circuit of $Z$ ($\iota_Z(v)$ the wire of vertex $v$; the input $v_r$ has wire $w_r$); output $k$ selects $F_k$. The **padding** of $C$ is
--   $$\mathrm{Pad}(C)=G_A(C,\diamond).$$
--   $\mathrm{Pad}(C)$ computes $C$; it is the form in which the obfuscator receives a circuit.
--
--   **Formalization Note.** `SLPBound cF cx` is the block-length property. Cells are 0-based (`Pad.cellA`, `cellB`, `cellX`, `cellY`, `cellYhat`, `cellQ`, `cellF`); vertex $j$ of a placed circuit goes to the $j$th cell of its region; a constant $0$ vertex gives an inactive cell and a constant $1$ vertex the instruction $1$. `GA`, `GB` and `PadC` are configurations (`p.toConfig` of the instruction data `Pad.gProg`); `⋄` is `none`; `UPad cx il ol s K = U il ol (Pad.M cx ol s K)`.
-- source:
--   Abram, Datta, Dutta, Roy, Obfuscation via Proofs of Equivalence and Polynomial-Time Reductions to Falsifiable Assumptions, STOC 2027 submission (manuscript sha256 f9518747…), p. 52, the choice of c_x and Definition 3.9; p. 47 (placement)

import Mathlib
import Definitions.Def_ObfEF_Incremental_Circuit
import Definitions.Def_ObfEF_Incremental_Formula
import Definitions.Def_ObfEF_Incremental_Cells

/-!
# The padding `U_{il,ol,s,K}`, the configurations `G_Z(C, C')` and `Pad(C)` (Definition 3.9)

Abram, Datta, Dutta, Roy, *Obfuscation via Proofs of Equivalence and Polynomial-Time Reductions to
Falsifiable Assumptions*, STOC 2027 submission (manuscript sha256 f9518747…), p. 52: the block
length `c_x` and Definition 3.9; p. 47: placement of a circuit in cells (Definition 3.3).

The block length. "We choose a constant `c_x` so that every formula over `→` and `⊥` of size at
most `c_F` is computed by the last instruction of a straight-line program of `c_x` instructions of
the forms `0, 1, ¬a, a ∧ b, a ∨ b`." `SLPBound cF cx` is this property; operands are variables of
the formula (`Sum.inl v`) or earlier instructions (`Sum.inr i`).

Layout (0-based cells, `M = 2s + 2·c_x·K + K + ol`): region `A` = cells `0, …, s-1`; region `B` =
cells `s, …, 2s-1`; extension block `X_i` (`i < K`) = cells `2s + c_x·i + m` (`m < c_x`); line
block `Y_i` = cells `2s + c_x·K + c_x·i + m`, whose last cell (`m = c_x - 1`) is `Ŷ_i`; the chain
`q_K, …, q_1` = cells `2s + 2c_xK, …, 2s + 2c_xK + K - 1` (so `q_t` is cell
`2s + 2c_xK + K - t`); `F_k` (`k < ol`) = cell `2s + 2c_xK + K + k`. The paper's line index
`i ∈ [K]` is `i - 1` here, and the chain position `t ∈ [K]` is `t` (`q_t`, `1 ≤ t ≤ K`).

Placement. Noninput vertex `j` of a circuit placed in a region starting at cell `base` goes to cell
`base + j` (canonical topological order = the vertex numbering). Its instruction is that of the
vertex with the outputs of the cells of its in-neighbours, or the input wires, as operands: a
constant `0` gives the inactive instruction `0`, a constant `1` the instruction `1`.
`⋄` (no circuit) is `none`.
-/

namespace ObfEF.Incremental

/-! ### Straight-line programs and the block length `c_x` -/

/-- An instruction of a straight-line program: `0`, `1`, `¬a`, `a ∧ b`, `a ∨ b`; an operand is a
variable (`inl v`) or an earlier instruction (`inr i`). -/
inductive SLInstr where
  | zero
  | one
  | neg (a : ℕ ⊕ ℕ)
  | and (a b : ℕ ⊕ ℕ)
  | or (a b : ℕ ⊕ ℕ)

namespace SLInstr

/-- The instruction-operands of an instruction. -/
def refs : SLInstr → List (ℕ ⊕ ℕ)
  | zero => []
  | one => []
  | neg a => [a]
  | and a b => [a, b]
  | or a b => [a, b]

/-- Value of the instruction when variables have values `α` and earlier instructions `v`. -/
def eval (α : ℕ → Bool) (v : ℕ → Bool) : SLInstr → Bool
  | zero => false
  | one => true
  | neg a => !(Sum.elim α v a)
  | and a b => Sum.elim α v a && Sum.elim α v b
  | or a b => Sum.elim α v a || Sum.elim α v b

end SLInstr

/-- Values of the instructions `P[0], …, P[m-1]` (instruction `i` may read instructions `< i`). -/
def slpEvalUpTo (α : ℕ → Bool) (P : List SLInstr) : ℕ → (ℕ → Bool)
  | 0 => fun _ => false
  | m + 1 =>
      let v := slpEvalUpTo α P m
      match P[m]? with
      | some ins => Function.update v m (ins.eval α v)
      | none => v

/-- `P` is a straight-line program: every instruction-operand refers to an earlier instruction. -/
def SLPWellFormed (P : List SLInstr) : Prop :=
  ∀ (m : ℕ) (hm : m < P.length), ∀ a ∈ (P[m]).refs, ∀ i : ℕ, a = Sum.inr i → i < m

/-- The formula `φ` is computed by the last instruction of the straight-line program `P`. -/
def SLPComputes (P : List SLInstr) (φ : Fml) : Prop :=
  SLPWellFormed P ∧ 1 ≤ P.length ∧
    ∀ α : ℕ → Bool, slpEvalUpTo α P P.length (P.length - 1) = φ.eval α

/-- `c_x` is a block length for `c_F`: every formula of size at most `c_F` is computed by the last
instruction of a straight-line program of exactly `c_x` instructions. -/
def SLPBound (cF cx : ℕ) : Prop :=
  ∀ φ : Fml, φ.size ≤ cF → ∃ P : List SLInstr, P.length = cx ∧ SLPComputes P φ

/-! ### The layout of `U_{il,ol,s,K}` -/

namespace Pad

/-- `M = 2s + 2c_xK + K + ol`. -/
def M (cx ol s K : ℕ) : ℕ := 2 * s + 2 * cx * K + K + ol

/-- Cell `j` of region `A`. -/
def cellA (j : ℕ) : ℕ := j
/-- Cell `j` of region `B`. -/
def cellB (s j : ℕ) : ℕ := s + j
/-- Cell `m` of the extension block `X_i` (`i < K`, `m < c_x`). -/
def cellX (cx s i m : ℕ) : ℕ := 2 * s + cx * i + m
/-- Cell `m` of the line block `Y_i`. -/
def cellY (cx s K i m : ℕ) : ℕ := 2 * s + cx * K + cx * i + m
/-- The last cell `Ŷ_i` of the line block `Y_i`. -/
def cellYhat (cx s K i : ℕ) : ℕ := cellY cx s K i (cx - 1)
/-- The chain cell `q_t` (`1 ≤ t ≤ K`); the chain cells are `q_K, …, q_1` in this order. -/
def cellQ (cx s K t : ℕ) : ℕ := 2 * s + 2 * cx * K + (K - t)
/-- The cell `F_k` (`k < ol`). -/
def cellF (cx s K k : ℕ) : ℕ := 2 * s + 2 * cx * K + K + k

/-- The `w`-index of the output of cell `j`. -/
def wCell (il j : ℕ) : ℕ := il + j

/-- `ι(v)`: the `w`-index of vertex `v` of a circuit placed from cell `base`. -/
def iota {il ol : ℕ} (C : Circuit (Fin il) ol) (base : ℕ) : Fin il ⊕ Fin C.size → ℕ
  | .inl r => r
  | .inr j => il + base + j

/-- The instruction of noninput vertex `j` of `C` placed from cell `base`. -/
def placedInstr {il ol : ℕ} (C : Circuit (Fin il) ol) (base : ℕ) (j : Fin C.size) : Instr :=
  match C.op j with
  | .const false => .zero
  | .const true => .one
  | .not a => .neg (iota C base (C.liftArg j a))
  | .and a b => .and (iota C base (C.liftArg j a)) (iota C base (C.liftArg j b))
  | .or a b => .or (iota C base (C.liftArg j a)) (iota C base (C.liftArg j b))

/-- The instruction of the cell at offset `j` of a region holding `C` (or `⋄`) from cell `base`:
the placed instruction for `j < |C|`, inactive otherwise. -/
def regionInstr {il ol : ℕ} (C : Option (Circuit (Fin il) ol)) (base j : ℕ) : Instr :=
  match C with
  | none => .zero
  | some C => if h : j < C.size then placedInstr C base ⟨j, h⟩ else .zero

/-- The instruction data of `G_Z(C, C')`, given the `w`-indices `out k` of the outputs `u_k` of
the circuit of region `Z` (`ι_Z(u_k)`). -/
def gProg (cx il ol s K : ℕ) (C C' : Option (Circuit (Fin il) ol)) (outZ : ℕ → ℕ) : Prog where
  instr j :=
    if j < s then regionInstr C 0 j
    else if j < 2 * s then regionInstr C' s (j - s)
    else if j < 2 * s + cx * K then .zero
    else if j < 2 * s + 2 * cx * K then
      (if (j - (2 * s + cx * K)) % cx = cx - 1 then .one else .zero)
    else if j < 2 * s + 2 * cx * K + K then
      -- the chain cell `q_t` with `t = K - (j - (2s + 2c_xK))`, identity order
      (let t := K - (j - (2 * s + 2 * cx * K))
       if t < K then .and (wCell il (cellYhat cx s K (t - 1))) (wCell il (cellQ cx s K (t + 1)))
       else .and (wCell il (cellYhat cx s K (K - 1))) (wCell il (cellYhat cx s K (K - 1))))
    else if j < M cx ol s K then
      .and (wCell il (cellQ cx s K 1)) (outZ (j - (2 * s + 2 * cx * K + K)))
    else .zero
  sel k := wCell il (cellF cx s K k)

/-- `ι_A(u_k)` for the circuit `C` of region `A`. -/
def outA {il ol : ℕ} (C : Circuit (Fin il) ol) (k : ℕ) : ℕ :=
  if h : k < ol then iota C 0 (C.out ⟨k, h⟩) else 0

/-- `ι_B(u_k)` for the circuit `C'` of region `B`. -/
def outB {il ol : ℕ} (s : ℕ) (C' : Circuit (Fin il) ol) (k : ℕ) : ℕ :=
  if h : k < ol then iota C' s (C'.out ⟨k, h⟩) else 0

end Pad

/-- The topology `U_{il,ol,s,K} = U_{il,ol,M}` with `M = 2s + 2c_xK + K + ol`. -/
def UPad (cx il ol s K : ℕ) : Wiring := U il ol (Pad.M cx ol s K)

/-- The configuration `G_A(C, C')`: `C` in region `A` (selected by the outputs), `C'` (or `⋄`) in
region `B`, extension blocks inactive, every `Ŷ_i = 1`, the other line-block cells inactive, the
chain in identity order, `F_k = q_1 ∧ ι_A(u_k)`, output `k` selecting `F_k`. -/
def GA (cx il ol s K : ℕ) (C : Circuit (Fin il) ol) (C' : Option (Circuit (Fin il) ol)) :
    Config :=
  (Pad.gProg cx il ol s K (some C) C' (Pad.outA C)).toConfig

/-- The configuration `G_B(C, C')`: as `G_A`, but `F_k = q_1 ∧ ι_B(u'_k)` for the outputs of the
circuit `C'` of region `B`. -/
def GB (cx il ol s K : ℕ) (C : Option (Circuit (Fin il) ol)) (C' : Circuit (Fin il) ol) :
    Config :=
  (Pad.gProg cx il ol s K C (some C') (Pad.outB s C')).toConfig

/-- The padding `Pad(C) = G_A(C, ⋄)`. -/
def PadC (cx il ol s K : ℕ) (C : Circuit (Fin il) ol) : Config :=
  GA cx il ol s K C none

end ObfEF.Incremental


