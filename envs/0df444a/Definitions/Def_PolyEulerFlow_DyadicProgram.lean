-- Prove2me | Definitions.Def_PolyEulerFlow_DyadicProgram
-- name    : PolyEulerFlow_DyadicProgram
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T07:18:59.855912+00:00
-- url     : https://prove2.me/theorems/32a89377-9ad1-4d97-9b67-cf0de2f445fc
-- title:
--   The dyadic two-stack normal form, its encoding, run and resetting halt
-- statement:
--   The compiled two-stack program of Theorem 1, in the dyadic normal form of §6.2 (pp.24–25).
--
--   A stack word $d_1\cdots d_H$ with digits $d_i\in\{1,2\}$ ($d_1$ on top) has the **code**
--   $$z_{\mathrm{stk}}=\sum_{i=1}^{H}d_i4^{-i},$$
--   and the empty stack has code $0$. Push of a digit $d$ and pop of the top digit act on codes as $(z+d)/4$ and $4z-d$. A **reader** $(y,\omega)$ starts at $y=xh$, $\omega=1/4$; while $\omega\ge h$ it reads $b=[y\ge\omega]$ and sets $y\leftarrow y-b\omega$, $\omega\leftarrow\omega/2$.
--
--   A **dyadic program** has a finite control set with an injective assignment of control bits, a start state, accepting and rejecting states, and a transition function that, from the control state, the status of each stack (empty, top digit one, top digit two), the reader bit $[y\ge\omega]$ and the reader-active bit $[\omega\ge h]$, selects the next state, one operation per stack (nothing, push one, push two, pop, reset) and one operation on the reader (hold, read, reset). A configuration is $(q,w_1,w_2,y,\omega)$. The **resetting halt**: a transition entering the accepting or rejecting state empties both stacks and sets $(y,\omega)=(0,0)$, and a configuration in a halting state is a fixed point. The run on input $x$ at scale $h$ starts at $(q_0,\varepsilon,\varepsilon,xh,1/4)$.
--
--   The **encoding** of a configuration is the vector of its control bits (as $0/1$), the codes of the two stacks, $y$ and $\omega$. The **linear part** of the selected transition is block diagonal: $1/4$, $4$, $1$ or $0$ on a stack for push, pop, nothing, reset; $\begin{pmatrix}1&-b\\0&1/2\end{pmatrix}$, $I$ or $0$ on the reader for read, hold, reset; $0$ on the control bits; and $0$ altogether for a halting transition or a halted configuration. A configuration at scale $2^{-s}$ is **valid** when both stacks have height at most $H_s=\lfloor(s-2)/2\rfloor$ and a selected pop is applied only to a nonempty stack.
--
--   **Formalization Note** Digits $1,2$ are represented by the two values of a two-element type. The page's normalized tests $y-\omega+h/4$ and $\omega-3h/4$ give the same two reader bits at every reader value the page uses, so the exact comparisons are used.
-- source:
--   Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript, sha256 c4e01b2b…), §6.2, pp.24–25 (PDF 26–27); proof of Lemma 24 and Lemma 25, pp.54–56 (PDF 56–58)

import Definitions.Def_PolyEulerFlow_eulerOrbit

namespace PolyEulerFlow

/-- The status of a stack: empty, top digit one, top digit two (the table on p.25). -/
inductive TopStatus
  | empty | one | two
  deriving DecidableEq

/-- Operations on a stack of the normal form: `push1`, `push2` are `(z + d)/4`, `pop` is `4z - d`. -/
inductive DOp
  | nop | push1 | push2 | pop | reset
  deriving DecidableEq

/-- Operations on the reader `(y, ω)`: `read` is `y ← y - bω, ω ← ω/2` (p.24). -/
inductive ROp
  | hold | read | reset
  deriving DecidableEq

/-- The dyadic two-stack normal form of §6.2, the compiled two-stack program of Theorem 1.
Bournez, One Polynomial Field for Every Euler Step and the Flow (manuscript, sha256 c4e01b2b…),
§6.2, pp.24–25.
**Formalization Note.** Stack digits `1, 2` are `Fin 2` values `0, 1`. `δ` reads the state, the two
stack statuses, the reader bit `[y ≥ ω]` and the reader-active test `[ω ≥ h]`; `ctrl` gives the control
bits. The page's tests `y - ω + h/4` and `ω - 3h/4` give the same two bits at every reader value the
page uses. -/
structure DyadicProgram where
  Q : Type
  [fintypeQ : Fintype Q]
  [decEqQ : DecidableEq Q]
  c : ℕ
  ctrl : Q → Fin c → Bool
  ctrl_injective : Function.Injective ctrl
  start : Q
  acc : Q
  rej : Q
  acc_ne_rej : acc ≠ rej
  δ : Q → TopStatus → TopStatus → Bool → Bool → Q × DOp × DOp × ROp

attribute [instance] DyadicProgram.fintypeQ DyadicProgram.decEqQ

namespace DyadicProgram

/-- The code `Σ dᵢ 4^{-i}` of a stack word `d₁ ⋯ d_H`, `d₁` the top; the empty stack has code zero
(p.24). `Fin 2` value `a` is the digit `a + 1`. -/
noncomputable def code : List (Fin 2) → ℝ
  | [] => 0
  | d :: w => (((d : ℕ) : ℝ) + 1 + code w) / 4

/-- A configuration of the program: control state, two stacks, reader value and weight. -/
structure Config (P : DyadicProgram) where
  q : P.Q
  st1 : List (Fin 2)
  st2 : List (Fin 2)
  y : ℝ
  ω : ℝ

/-- The status of a stack. -/
def status : List (Fin 2) → TopStatus
  | [] => .empty
  | d :: _ => if d = 0 then .one else .two

/-- The effect of an operation on a stack word. -/
def applyD : DOp → List (Fin 2) → List (Fin 2)
  | .nop, w => w
  | .push1, w => 0 :: w
  | .push2, w => 1 :: w
  | .pop, w => w.tail
  | .reset, _ => []

/-- The transition selected at a configuration. -/
noncomputable def instr (P : DyadicProgram) (h : ℝ) (C : P.Config) : P.Q × DOp × DOp × ROp :=
  open Classical in
  P.δ C.q (status C.st1) (status C.st2) (decide (C.ω ≤ C.y)) (decide (h ≤ C.ω))

/-- The reader bit `[y ≥ ω]`. -/
noncomputable def readerBit {P : DyadicProgram} (C : P.Config) : ℝ :=
  open Classical in
  if C.ω ≤ C.y then 1 else 0

/-- The state is accepting or rejecting. -/
def IsHaltState (P : DyadicProgram) (q : P.Q) : Prop :=
  q = P.acc ∨ q = P.rej

/-- One transition. **Resetting halt** (p.55): a transition entering `acc` or `rej` empties both stacks
and sets `(y, ω)` to `(0, 0)`; a configuration with state `acc` or `rej` is a fixed point. -/
noncomputable def step (P : DyadicProgram) (h : ℝ) (C : P.Config) : P.Config :=
  open Classical in
  if P.IsHaltState C.q then C
  else
    let r := P.instr h C
    if P.IsHaltState r.1 then ⟨r.1, [], [], 0, 0⟩
    else
      ⟨r.1, applyD r.2.1 C.st1, applyD r.2.2.1 C.st2,
        match r.2.2.2 with
        | .hold => C.y
        | .read => C.y - readerBit C * C.ω
        | .reset => 0,
        match r.2.2.2 with
        | .hold => C.ω
        | .read => C.ω / 2
        | .reset => 0⟩

/-- The initial configuration at input `x` and scale `h`: `y = xh`, `ω = 1/4` (p.24), stacks empty. -/
noncomputable def init (P : DyadicProgram) (x : ℕ) (h : ℝ) : P.Config :=
  ⟨P.start, [], [], (x : ℝ) * h, 1 / 4⟩

/-- The `j`-th configuration on input `x` at scale `h`. -/
noncomputable def conf (P : DyadicProgram) (x : ℕ) (h : ℝ) (j : ℕ) : P.Config :=
  (P.step h)^[j] (P.init x h)

/-- The encoding of a configuration: control bits as `0/1`, then the codes of both stacks, then
`y` and `ω`. These are the data registers of the realization. -/
noncomputable def enc (P : DyadicProgram) (C : P.Config) : Fin P.c ⊕ Fin 4 → ℝ
  | .inl i => if P.ctrl C.q i then 1 else 0
  | .inr a => ![code C.st1, code C.st2, C.y, C.ω] a

/-- The scalar linear gain of a stack operation: `1/4` for a push, `4` for a pop, `0` for a reset. -/
noncomputable def gain : DOp → ℝ
  | .nop => 1
  | .push1 => 1 / 4
  | .push2 => 1 / 4
  | .pop => 4
  | .reset => 0

/-- The linear part on the reader block `(y, ω)`: `(1, -b; 0, 1/2)` for a read (p.55). -/
noncomputable def readerBlock (b : ℝ) : ROp → Matrix (Fin 2) (Fin 2) ℝ
  | .hold => 1
  | .read => !![1, -b; 0, 1 / 2]
  | .reset => 0

/-- The linear part `D_σ` of the transition selected at `C`, block diagonal on stacks and reader,
zero on the control bits (pp.55–56). A transition into a halting state, and a halted configuration,
have the zero linear part: their branch is constant. -/
noncomputable def linearPart (P : DyadicProgram) (h : ℝ) (C : P.Config) :
    Matrix (Fin P.c ⊕ Fin 4) (Fin P.c ⊕ Fin 4) ℝ :=
  open Classical in
  let r := P.instr h C
  if P.IsHaltState C.q ∨ P.IsHaltState r.1 then 0
  else
    let R := readerBlock (readerBit C) r.2.2.2
    Matrix.fromBlocks 0 0 0
      !![gain r.2.1, 0, 0, 0;
         0, gain r.2.2.1, 0, 0;
         0, 0, R 0 0, R 0 1;
         0, 0, R 1 0, R 1 1]

/-- A valid configuration at scale `h = 2^{-s}`: heights at most `H_s = ⌊(s - 2)/2⌋` (p.24), and pop is
only selected on a nonempty stack ("only used on a valid stack", p.24).
**Formalization Note.** `(s - 2) / 2` is natural-number arithmetic; `H_s = 0` for `s ≤ 3`. -/
def IsValidConfig (P : DyadicProgram) (s : ℕ) (C : P.Config) : Prop :=
  C.st1.length ≤ (s - 2) / 2 ∧ C.st2.length ≤ (s - 2) / 2 ∧
    (¬ P.IsHaltState C.q → ¬ P.IsHaltState (P.instr (scale s) C).1 →
      ((P.instr (scale s) C).2.1 = .pop → C.st1 ≠ []) ∧
      ((P.instr (scale s) C).2.2.1 = .pop → C.st2 ≠ []))

end DyadicProgram

end PolyEulerFlow


