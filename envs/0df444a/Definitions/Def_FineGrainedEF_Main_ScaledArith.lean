-- Prove2me | Definitions.Def_FineGrainedEF_Main_ScaledArith
-- name    : FineGrainedEF_Main_ScaledArith
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T01:10:26.04604+00:00
-- url     : https://prove2.me/theorems/074c2464-3e75-4e01-bde5-374cf130e4e6
-- title:
--   Scaled real and complex words of A.2–A.3: promotion, Add, Sub, Mul, Round and embedding
-- statement:
--   A **scaled real word** $(A;f)\in D_{f,w}$ has a signed $w$-bit numerator $A$ and a scale $f$ (a parameter, not a wire) and represents $A\,2^{-f}$ (p. 45). A **scaled complex word** in $C_{f,w}=D_{f,w}\times D_{f,w}$ has two signed numerators of a common width and represents $(A+iB)2^{-f}$ (p. 47).
--
--   - **Promotion** $\mathrm{Prmt}_{f\to g}(A;f)=(2^{g-f}A;g)$, $g\ge f$: a left shift (p. 46).
--   - **Addition / subtraction** (omitted-index rule, p. 46): promote both operands to $k=\max(\mathrm{sc}\,x,\mathrm{sc}\,y)$ and apply AddInt / SubInt to the numerators; complex operands componentwise.
--   - **Multiplication** $\mathrm{Mul}_{f,g}$: numerator MulInt, scale $f+g$ (real); for complex operands the numerators are $\mathrm{SubInt}(\mathrm{MulInt}(A,B),\mathrm{MulInt}(A',B'))$ and $\mathrm{AddInt}(\mathrm{MulInt}(A,B'),\mathrm{MulInt}(A',B))$, width $w_1+w_2+1$ (p. 47).
--   - **Exact division** $x/2^k$: the scale increases by $k$ (p. 48).
--   - **Rounding** $\mathrm{Round}(x)=\lfloor x+1/2\rfloor$ (p. 47): for $x=(A;f)$, $f\ge1$, $T:=\mathrm{AddInt}(A,2^{f-1})$ in $b=\max(w,f+1)+1$ bits and the output $(Q;0)$ with $Q=(T_f,\dots,T_{b-1})$; identity at $f=0$.
--   - **Embedding** $x\mapsto x+i0$: the imaginary numerator is hardwired to zero at the same width and scale (p. 47).
--   - Hardwired complex constants have given integer numerators at a given scale and width.
--
--   **Formalization Note.** `SReal` (`num`, `sc`), `SCpx` (`re`, `im`, `sc`), `prmt`, `add`, `sub`, `mul`, `round`, `divPow2`, `signExt`, `width`, `embed`, `cpxConst`. Every operator keeps its full result; widths follow from the operand widths.
-- source:
--   Krapivin, Li, Shi, Fine-Grained Proof Complexity for Elementary Arithmetic in Extended Frege, STOC 2027 submission (manuscript sha256 704dfb8a…), pp. 45-48, §A.2-A.3

import Mathlib
import Definitions.Def_FineGrainedEF_Main_EF
import Definitions.Def_FineGrainedEF_Main_BoolCircuits
import Definitions.Def_FineGrainedEF_Main_IntCircuits

namespace FineGrainedEF.Main

/-- A scaled real word `(A; f) ∈ D_{f,w}` (p. 45): a signed numerator `A` of `w` wires and a scale
`f` (a parameter, not a wire); it represents `A · 2^{-f}`. -/
structure SReal where
  num : List ℕ
  sc : ℕ
  deriving Inhabited

/-- A scaled complex word in `C_{f,w} = D_{f,w} × D_{f,w}` (p. 47): signed numerators `re`, `im`
of a common width at the common scale `sc`; it represents `(re + i·im) · 2^{-sc}`. -/
structure SCpx where
  re : List ℕ
  im : List ℕ
  sc : ℕ
  deriving Inhabited

/-- `Prmt_{f→g}` (p. 46): for `g ≥ f`, the exact wiring `(A; f) ↦ (2^{g-f} A; g)`. (Unchanged if
`g < f`; never used so.) -/
def SReal.prmt (g : ℕ) (x : SReal) : Build SReal :=
  if x.sc ≤ g then do
    let n ← shl (g - x.sc) x.num
    pure ⟨n, g⟩
  else pure x

/-- `x ± y` with `Add_f` / `Sub_f` and the omitted-operator-index rule (p. 46): promote both to
`k = max(sc x, sc y)` and apply `AddInt` / `SubInt` to the numerators; width
`max(w₁, w₂) + 1` after promotion. -/
def SReal.add (x y : SReal) : Build SReal := do
  let k := max x.sc y.sc
  let x' ← x.prmt k
  let y' ← y.prmt k
  let n ← addInt x'.num y'.num
  pure ⟨n, k⟩

def SReal.sub (x y : SReal) : Build SReal := do
  let k := max x.sc y.sc
  let x' ← x.prmt k
  let y' ← y.prmt k
  let n ← subInt x'.num y'.num
  pure ⟨n, k⟩

/-- `Mul_{f,g}` (p. 46): numerator `MulInt`, scale `f + g`, width `w₁ + w₂`. -/
def SReal.mul (x y : SReal) : Build SReal := do
  let n ← mulInt x.num y.num
  pure ⟨n, x.sc + y.sc⟩

/-- `Round(x) := ⌊x + 1/2⌋` (p. 47): for `x = (A; f)`, `f ≥ 1`, compute
`T := AddInt(A, 2^{f-1})` (the literal `2^{f-1}` as an `(f+1)`-bit signed constant) in
`b = max(w, f+1) + 1` bits and return `(Q; 0)` with `Q = (T_f, …, T_{b-1})`, the low `b - f` bits
of the quotient circuit `⌊T / 2^f⌋`. At `f = 0`, rounding is the identity. -/
def SReal.round (x : SReal) : Build SReal :=
  if x.sc = 0 then pure x
  else do
    let c ← intConst ((2 : ℤ) ^ (x.sc - 1)) (x.sc + 1)
    let T ← addInt x.num c
    pure ⟨T.drop x.sc, 0⟩

/-- Promotion of a complex word: both components (p. 48). -/
def SCpx.prmt (g : ℕ) (x : SCpx) : Build SCpx :=
  if x.sc ≤ g then do
    let r ← shl (g - x.sc) x.re
    let i ← shl (g - x.sc) x.im
    pure ⟨r, i, g⟩
  else pure x

/-- Complex addition and subtraction: the real operators componentwise (p. 47), after promotion
to the larger scale. -/
def SCpx.add (x y : SCpx) : Build SCpx := do
  let k := max x.sc y.sc
  let x' ← x.prmt k
  let y' ← y.prmt k
  let r ← addInt x'.re y'.re
  let i ← addInt x'.im y'.im
  pure ⟨r, i, k⟩

def SCpx.sub (x y : SCpx) : Build SCpx := do
  let k := max x.sc y.sc
  let x' ← x.prmt k
  let y' ← y.prmt k
  let r ← subInt x'.re y'.re
  let i ← subInt x'.im y'.im
  pure ⟨r, i, k⟩

/-- Complex `Mul_{f,g}` (p. 47): for `x = (A + iA')2^{-f}`, `y = (B + iB')2^{-g}`, numerators
`SubInt(MulInt(A, B), MulInt(A', B'))` and `AddInt(MulInt(A, B'), MulInt(A', B))`, scale `f + g`,
width `w₁ + w₂ + 1`. -/
def SCpx.mul (x y : SCpx) : Build SCpx := do
  let ab ← mulInt x.re y.re
  let ab' ← mulInt x.im y.im
  let r ← subInt ab ab'
  let ab'' ← mulInt x.re y.im
  let a'b ← mulInt x.im y.re
  let i ← addInt ab'' a'b
  pure ⟨r, i, x.sc + y.sc⟩

/-- `x / 2^k` (p. 48): only the scale increases. -/
def SCpx.divPow2 (k : ℕ) (x : SCpx) : SCpx := ⟨x.re, x.im, x.sc + k⟩

/-- Sign-extension of both components to width `w`. -/
def SCpx.signExt (w : ℕ) (x : SCpx) : Build SCpx := do
  let r ← FineGrainedEF.Main.signExt w x.re
  let i ← FineGrainedEF.Main.signExt w x.im
  pure ⟨r, i, x.sc⟩

/-- Component width of a complex word. -/
def SCpx.width (x : SCpx) : ℕ := max x.re.length x.im.length

/-- Embedding of a real word `x` as `x + i0` (p. 47): imaginary numerator hardwired to zero, of the
same width, same scale. -/
def SReal.embed (x : SReal) : Build SCpx := do
  let z ← constWord 0 x.num.length
  pure ⟨x.num, z, x.sc⟩

/-- A hardwired complex constant with integer numerators `(re, im)` at scale `f`, both of width
`w` (two's complement). -/
def cpxConst (v : ℤ × ℤ) (f w : ℕ) : Build SCpx := do
  let r ← intConst v.1 w
  let i ← intConst v.2 w
  pure ⟨r, i, f⟩

end FineGrainedEF.Main


