-- Prove2me | Definitions.Def_OAI_Analysis_BoxTransport_Expressions
-- name    : OAI_Analysis_BoxTransport_Expressions
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T13:09:33.200401+00:00
-- url     : https://prove2.me/theorems/d7aa3e37-7fa0-4456-b1cd-e5beb4b6c3a8
-- title:
--   Smooth expressions on space-time: symbolic derivatives, error bounds and computable rational evaluation
-- statement:
--   This file introduces a small language of explicit smooth functions on space-time $\mathbb{R}\times\mathbb{R}^3$, with exact symbolic partial derivatives, explicit size and error bounds, and computable rational evaluation. Points are $p=(t,x_0,x_1,x_2)$ with the max norm $\|p\|=\max(|t|,|x_0|,|x_1|,|x_2|)$. A rational code is a triple $(u,s,d)\in\mathbb{N}^3$ denoting the rational $[(u,s,d)]=(u-s)/(d+1)$, and every rational has a code. Let $\psi(y)=e^{-1/y}$ for $y>0$ and $\psi(y)=0$ for $y\le0$, and $f_m(y)=y^{-m}\psi(y)$ for $m\in\mathbb{N}$, so $f_0=\psi$.
--
--   1. **Expressions and their values.** Expressions are finite trees whose leaves are the coordinates $t,x_0,x_1,x_2$ and whose nodes are sums $e+f$, products $e\cdot f$, negations $-e$, and unary nodes $\mathrm{u}_k(e)$ with an index $k\in\mathbb{N}$. The value of an expression $e$ is the function $v_e:\mathbb{R}\times\mathbb{R}^3\to\mathbb{R}$ obtained by reading leaves as coordinate functions, sums, products and negations literally, and
--   $$v_{\mathrm{u}_k(e)}(p)=\begin{cases}[\gamma_{k/3}] & k\equiv0\pmod 3,\\ v_e(p)^{-1} & k\equiv1\pmod 3,\\ f_{\lfloor k/3\rfloor}\bigl(v_e(p)\bigr) & k\equiv2\pmod 3,\end{cases}$$
--   where $\gamma_0,\gamma_1,\gamma_2,\dots$ is the standard enumeration of rational codes. Accordingly, the constant expression $\mathrm{cst}(q)=\mathrm{u}_{3\,\mathrm{idx}(q)}(t)$, with $\mathrm{idx}(q)$ the position of the code $q$ in the enumeration, has value $[q]$; $\mathrm{inv}_b(e)=\mathrm{u}_{3b+1}(e)$ has value $1/v_e$; and $\mathrm{flat}_m(e)=\mathrm{u}_{3m+2}(e)$ has value $f_m\circ v_e$.
--
--   2. **Validity and smoothness.** An expression is valid if every reciprocal node $\mathrm{inv}_b(e')$ occurring in it satisfies $|v_{e'}(p)|\ge 1/(b+1)$ for all $p\in\mathbb{R}\times\mathbb{R}^3$. The value of every valid expression is $C^\infty$ on $\mathbb{R}\times\mathbb{R}^3$.
--
--   3. **Symbolic derivatives.** For an axis $\delta\in\{t,x_0,x_1,x_2\}$ the derivative $\partial_\delta e$ is defined by structural recursion: a leaf goes to the constant $1$ if it is the coordinate $\delta$ and to the constant $0$ otherwise; $\partial_\delta(e+f)=\partial_\delta e+\partial_\delta f$; $\partial_\delta(e\cdot f)=\partial_\delta e\cdot f+e\cdot\partial_\delta f$; $\partial_\delta(-e)=-\partial_\delta e$; constant nodes go to $0$; and
--   $$\partial_\delta\,\mathrm{inv}_b(e)=-\bigl(\mathrm{inv}_b(e)\cdot\mathrm{inv}_b(e)\bigr)\cdot\partial_\delta e,\qquad \partial_\delta\,\mathrm{flat}_m(e)=\Bigl(\mathrm{flat}_{m+2}(e)+\bigl(-(m\cdot\mathrm{flat}_{m+1}(e))\bigr)\Bigr)\cdot\partial_\delta e .$$
--   If $e$ is valid, then $\partial_\delta e$ is valid and $v_{\partial_\delta e}(p)=\frac{\partial v_e}{\partial\delta}(p)$ for every $p$. For a list of axes $(\delta_1,\dots,\delta_r)$ the iterated derivative is $\partial_{\delta_1}\partial_{\delta_2}\cdots\partial_{\delta_r}e$, the innermost derivative being taken along $\delta_r$.
--
--   4. **Size bounds and error amplification.** For $R\in\mathbb{N}$ define $B_R(e)\in\mathbb{N}$ recursively by $B_R=R$ on leaves, $B_R(e+f)=B_R(e)+B_R(f)$, $B_R(e\cdot f)=B_R(e)\,B_R(f)$, $B_R(-e)=B_R(e)$, $B_R=u+s$ for a constant node with code $(u,s,d)$, $B_R(\mathrm{inv}_b(e))=b+1$ and $B_R(\mathrm{flat}_m(e))=m!$; it serves as a bound for $|v_e(p)|$ when $e$ is valid and $\|p\|\le R$. The amplification factor $A_R(e)\in\mathbb{N}$ is $0$ on leaves and constant nodes, additive on sums, unchanged by negation, and
--   $$A_R(e\cdot f)=\bigl(B_R(e)+A_R(e)\bigr)A_R(f)+B_R(f)\,A_R(e),\qquad A_R(\mathrm{inv}_b(e))=2(b+1)^2A_R(e),\qquad A_R(\mathrm{flat}_m(e))=L_m\,A_R(e)+1,$$
--   with $L_m=(m+2)!+m\,(m+1)!$. For a triple of expressions $(e_0,e_1,e_2)$ and a list of axes $\Delta$, the family bound is $\sum_{c=0}^{2}B_R(\partial_\Delta e_c)$, and the gradient bound is the sum of the family bounds for the four lists obtained by prepending $t$, $x_0$, $x_1$ or $x_2$ to $\Delta$.
--
--   5. **Rational evaluation.** A rational point code $q$ is a quadruple of rational codes $(q_t,q_0,q_1,q_2)$ and denotes the point $\bar q=([q_t],[q_0],[q_1],[q_2])$. For a precision $N\in\mathbb{N}$ the evaluation $E_N(q,e)$ is the rational code computed recursively: leaves return the corresponding coordinate code; sums, products and negations use exact rational arithmetic on codes; a constant node returns its code; a reciprocal node $\mathrm{inv}_b(e)$ returns the guarded inverse of $r=E_N(q,e)$, namely $r^{-1}$ if $|[r]|\ge 1/(2(b+1))$ and $0$ otherwise; and $\mathrm{flat}_m(e)$ returns a rational approximation, within $1/(N+1)$, of $f_m([r])$ with $r=E_N(q,e)$, obtained from a truncated exponential series. With $R_q=\sum_{c}(u_c+s_c)$ summed over the four coordinate codes $q_c=(u_c,s_c,d_c)$, the precise evaluation is
--   $$\operatorname{Eval}(e,q,N)=E_{N'}(q,e),\qquad N'=(N+1)\bigl(A_{R_q}(e)+1\bigr).$$
--   The amplification factor is designed so that $|v_e(\bar q)-[E_N(q,e)]|\le A_R(e)/(N+1)$ for valid $e$ whenever $\|\bar q\|\le R$, which makes the precise evaluation accurate to within $1/(N+1)$.
--
--   6. **Computability.** The constructors, the symbolic derivative as a function of the axis and the expression, iterated derivatives, $B_R(e)$ and $A_R(e)$ as functions of $(R,e)$, the family and gradient bounds (for fixed $R$ and a fixed triple, as functions of the list of axes), the guarded inverse and $R_q$ are primitive recursive, and $E_N(q,e)$ and $\operatorname{Eval}(e,q,N)$ are computable functions of all their arguments.
--
--   7. **Representable functions.** A function $g:\mathbb{R}\times\mathbb{R}^3\to\mathbb{R}$ is representable if $g=v_e$ for some valid expression $e$. The representable functions contain every rational constant (in particular natural numbers, $0$ and $1$) and the coordinate functions $t,x_0,x_1,x_2$, and they are closed under sums, products, negation, differences, division by a rational or natural-number constant, composition with $f_m$, with $\psi$ and with the smooth transition $S(y)=\psi(y)/(\psi(y)+\psi(1-y))$, reciprocals $1/g$ and quotients $g/h$ whenever $|g|$, respectively $|h|$, is bounded below by a positive constant on all of $\mathbb{R}\times\mathbb{R}^3$, partial derivatives along each of the four axes, and finite sums and products. Every representable function is $C^\infty$. Two auxiliary facts are recorded: $\psi(\tfrac12)\le\psi(y)+\psi(1-y)$ for all $y\in\mathbb{R}$, and for every $\varepsilon>0$ there is $b\in\mathbb{N}$ with $1/(b+1)\le\varepsilon$.
--
--   This calculus is the tool for the effectivity part of admissibility: when every component of a smooth, compactly supported vector field is representable, all of its mixed partial derivatives are represented by expressions produced by a primitive recursive procedure, their values at rational points can be computed to any requested precision, and the size bounds supply computable bounds and moduli of continuity.
--
--   **Formalization Note** Expressions are Mathlib's codes of partial recursive functions, `Nat.Partrec.Code`, reused purely as syntax trees so that their encoding and primitive recursion principle are available: `zero`, `succ`, `left`, `right` stand for $t,x_0,x_1,x_2$, `pair` for the sum, `comp` for the product, `rfind'` for negation, and `prec m e` for the unary node with index `Encodable.encode m` (the helper `node k e` uses `Denumerable.ofNat Expr k`, so its index is exactly $k$). The constructors are `cst`, `invE`, `flatE`, `varE`; the value is `value`, validity `Valid`, derivatives `diff` and `mixedE`, bounds `boundE`, `ampE`, `familyBound`, `gradientBound`, evaluation `evalE` and `evalPrecise`, with `unaryValue`, `diffUnary`, `unaryBound`, `unaryAmp`, `unaryEval`, `qGuardInv` and `pointBound` the per-node pieces and $R_q$. Partial derivatives are `fderiv` applied to a coordinate direction. The `primrec_*`, `pr_*`, `*_eq_rec` and `computable_*` lemmas establish item 6, the `value_*` and `valid_*` lemmas are simp rules, `smooth_value`, `valid_diff` and `value_diff` give items 2 and 3, the `Representable` namespace gives item 7, and `ite_eq_left` is a private helper. The bound and error properties of $B_R$ and $A_R$ are proved as separate results.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/BoxTransport/Expressions.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/BoxTransport/Expressions.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BalancedBoxRouting mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BalancedBoxRouting
import Definitions.Def_OAI_Analysis_BoxTransport_Geometry
import Definitions.Def_OAI_Analysis_BoxTransport_Flow
import Definitions.Def_OAI_Analysis_BoxTransport_Motion
import Definitions.Def_OAI_Analysis_BoxTransport_Computation

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e

namespace OAI

/-! Smooth expression calculus and effective mixed derivatives. -/

noncomputable section
open scoped Topology
open scoped BigOperators ContDiff

open scoped BigOperators ContDiff
open Nat.Partrec (Code)
namespace BoxTransport.Routing.Computation

abbrev Expr := Code

def node (m : ℕ) (e : Expr) : Expr := .prec (Denumerable.ofNat Expr m) e

def cst (q : QCode) : Expr := node (3 * Encodable.encode q) .zero

def invE (b : ℕ) (e : Expr) : Expr := node (3 * b + 1) e

def flatE (m : ℕ) (e : Expr) : Expr := node (3 * m + 2) e

def varE : Axis → Expr
  | none => .zero
  | some j => if j = 0 then .succ else if j = 1 then .left else .right

noncomputable def unaryValue (m : ℕ) (x : ℝ) : ℝ :=
  if m % 3 = 0 then Qval (Denumerable.ofNat QCode (m / 3))
  else if m % 3 = 1 then x⁻¹ else flatTerm (m / 3) x

noncomputable def value : Expr → SpaceTime → ℝ
  | .zero, p => p.1
  | .succ, p => p.2 0
  | .left, p => p.2 1
  | .right, p => p.2 2
  | .pair e f, p => value e p + value f p
  | .comp e f, p => value e p * value f p
  | .prec m e, p => unaryValue (Encodable.encode m) (value e p)
  | .rfind' e, p => -value e p

def Valid : Expr → Prop
  | .zero | .succ | .left | .right => True
  | .pair e f | .comp e f => Valid e ∧ Valid f
  | .prec m e => Valid e ∧ (Encodable.encode m % 3 = 1 →
      ∀ p, ((Encodable.encode m / 3 : ℕ) + 1 : ℝ)⁻¹ ≤ |value e p|)
  | .rfind' e => Valid e

@[simp] theorem value_node (m : ℕ) (e : Expr) (p : SpaceTime) :
    value (node m e) p = unaryValue m (value e p) := by simp [value, node]
@[simp] theorem value_cst (q : QCode) (p : SpaceTime) : value (cst q) p = (Qval q : ℝ) := by
  rw [cst, value_node]
  rw [unaryValue, ite_eq_left (by omega), Nat.mul_div_right _ (by omega), Denumerable.ofNat_encode]
@[simp] theorem value_invE (b : ℕ) (e : Expr) (p : SpaceTime) : value (invE b e) p = (value e p)⁻¹ := by
  simp [invE, unaryValue]
@[simp] theorem value_flatE (m : ℕ) (e : Expr) (p : SpaceTime) : value (flatE m e) p = flatTerm m (value e p) := by
  simp [flatE, unaryValue, Nat.mul_add_div (by omega : 0 < 3)]
@[simp] theorem valid_node (m : ℕ) (e : Expr) : Valid (node m e) ↔
    Valid e ∧ (m % 3 = 1 → ∀ p, ((m / 3 : ℕ) + 1 : ℝ)⁻¹ ≤ |value e p|) := by
  simp [Valid, node]
@[simp] theorem valid_cst (q : QCode) : Valid (cst q) := by simp [cst, Valid]
@[simp] theorem valid_flatE (m : ℕ) (e : Expr) : Valid (flatE m e) ↔ Valid e := by
  simp [flatE]
@[simp] theorem valid_invE (b : ℕ) (e : Expr) : Valid (invE b e) ↔
    Valid e ∧ ∀ p, ((b : ℝ) + 1)⁻¹ ≤ |value e p| := by simp [invE, Nat.mul_add_div (by omega : 0 < 3)]

@[simp] theorem value_varE (j : Axis) (p : SpaceTime) :
    value (varE j) p = match j with | none => p.1 | some i => p.2 i := by
  cases j with
  | none => rfl
  | some i => fin_cases i <;> simp [varE, value]
@[simp] theorem valid_varE (j : Axis) : Valid (varE j) := by
  cases j with
  | none => trivial
  | some i => fin_cases i <;> simp [varE, Valid]

theorem nonzero_of_inverse_bound {b : ℕ} {x : ℝ} (h : ((b : ℝ) + 1)⁻¹ ≤ |x|) : x ≠ 0 := by
  have hp : (0 : ℝ) < ((b : ℝ) + 1)⁻¹ := by positivity
  exact abs_pos.mp (hp.trans_le h)

theorem smooth_value {e : Expr} (he : Valid e) : ContDiff ℝ ∞ (value e) := by
  induction e with
  | zero => exact contDiff_fst
  | succ => exact (contDiff_apply ℝ ℝ (0 : Fin 3)).comp contDiff_snd
  | left => exact (contDiff_apply ℝ ℝ (1 : Fin 3)).comp contDiff_snd
  | right => exact (contDiff_apply ℝ ℝ (2 : Fin 3)).comp contDiff_snd
  | pair e f ih₁ ih₂ => exact (ih₁ he.1).add (ih₂ he.2)
  | comp e f ih₁ ih₂ => exact (ih₁ he.1).mul (ih₂ he.2)
  | rfind' e ih => exact (ih he).neg
  | prec m e _ ih =>
    change ContDiff ℝ ∞ (fun p => unaryValue (Encodable.encode m) (value e p))
    unfold unaryValue
    split_ifs with h₀ h₁
    · exact contDiff_const
    · exact (ih he.1).inv (fun p => nonzero_of_inverse_bound (he.2 h₁ p))
    · exact (contDiff_flatTerm _).comp (ih he.1)

def diffUnary (n : ℕ) (e de : Expr) : Expr :=
  if n % 3 = 0 then cst qZero
  else if n % 3 = 1 then .rfind' (.comp (.comp (invE (n / 3) e) (invE (n / 3) e)) de)
  else .comp (.pair (flatE (n / 3 + 2) e)
    (.rfind' (.comp (cst (qNat (n / 3))) (flatE (n / 3 + 1) e)))) de

def diff (j : Axis) : Expr → Expr
  | .zero => cst (if j = none then qOne else qZero)
  | .succ => cst (if j = some 0 then qOne else qZero)
  | .left => cst (if j = some 1 then qOne else qZero)
  | .right => cst (if j = some 2 then qOne else qZero)
  | .pair e f => .pair (diff j e) (diff j f)
  | .comp e f => .pair (.comp (diff j e) f) (.comp e (diff j f))
  | .prec m e => diffUnary (Encodable.encode m) e (diff j e)
  | .rfind' e => .rfind' (diff j e)

theorem valid_diff {e : Expr} (he : Valid e) (j : Axis) : Valid (diff j e) := by
  induction e with
  | zero | succ | left | right => exact valid_cst _
  | pair e f ih₁ ih₂ => exact ⟨ih₁ he.1, ih₂ he.2⟩
  | comp e f ih₁ ih₂ => exact ⟨⟨ih₁ he.1, he.2⟩, he.1, ih₂ he.2⟩
  | rfind' e ih => exact ih he
  | prec m e _ ih =>
    dsimp [diff, diffUnary]
    split_ifs with h₀ h₁
    · exact valid_cst _
    · have hi : Valid (invE (Encodable.encode m / 3) e) := (valid_invE _ _).2 ⟨he.1, he.2 h₁⟩
      exact ⟨⟨hi, hi⟩, ih he.1⟩
    · exact ⟨⟨(valid_flatE _ _).2 he.1, valid_cst _, (valid_flatE _ _).2 he.1⟩, ih he.1⟩

theorem value_diff {e : Expr} (he : Valid e) (j : Axis) (p : SpaceTime) :
    value (diff j e) p = fderiv ℝ (value e) p (coordinateDirection j) := by
  induction e with
  | zero =>
    cases j with
    | none => simp [diff, value, coordinateDirection, fderiv_fst]
    | some i => simp [diff, value, coordinateDirection, fderiv_fst]
  | succ =>
    have hd : fderiv ℝ (value Code.succ) p =
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0).comp
          (ContinuousLinearMap.snd ℝ ℝ Space) :=
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 0).comp
        (ContinuousLinearMap.snd ℝ ℝ Space)).hasFDerivAt.fderiv
    rw [hd]
    cases j with
    | none => simp [diff, coordinateDirection]
    | some i => fin_cases i <;> simp [diff, coordinateDirection, coordinateVector]
  | left =>
    have hd : fderiv ℝ (value Code.left) p =
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 1).comp
          (ContinuousLinearMap.snd ℝ ℝ Space) :=
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 1).comp
        (ContinuousLinearMap.snd ℝ ℝ Space)).hasFDerivAt.fderiv
    rw [hd]
    cases j with
    | none => simp [diff, coordinateDirection]
    | some i => fin_cases i <;> simp [diff, coordinateDirection, coordinateVector]
  | right =>
    have hd : fderiv ℝ (value Code.right) p =
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 2).comp
          (ContinuousLinearMap.snd ℝ ℝ Space) :=
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 3 => ℝ) 2).comp
        (ContinuousLinearMap.snd ℝ ℝ Space)).hasFDerivAt.fderiv
    rw [hd]
    cases j with
    | none => simp [diff, coordinateDirection]
    | some i => fin_cases i <;> simp [diff, coordinateDirection, coordinateVector]
  | pair e f ih₁ ih₂ =>
    have he' := (smooth_value he.1).differentiable (by simp)
    have hf' := (smooth_value he.2).differentiable (by simp)
    rw [diff, value, ih₁ he.1, ih₂ he.2]
    exact (congrArg (fun L : SpaceTime →L[ℝ] ℝ => L (coordinateDirection j))
      ((he' p).hasFDerivAt.add (hf' p).hasFDerivAt).fderiv).symm
  | comp e f ih₁ ih₂ =>
    have he' := (smooth_value he.1).differentiable (by simp)
    have hf' := (smooth_value he.2).differentiable (by simp)
    simp only [diff, value, ih₁ he.1, ih₂ he.2]
    have hd := ((he' p).hasFDerivAt.mul (hf' p).hasFDerivAt).fderiv
    change fderiv ℝ (fun p => value e p * value f p) p = _ at hd
    rw [hd]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  | rfind' e ih =>
    have he' := (smooth_value (e := e) he).differentiable (by simp)
    simp only [diff, value, ih he]
    have hd := (he' p).hasFDerivAt.neg.fderiv
    change fderiv ℝ (fun p => -value e p) p = _ at hd
    rw [hd]
    rfl
  | prec m e _ ih =>
    have he' := (smooth_value he.1).differentiable (by simp)
    change value (diffUnary (Encodable.encode m) e (diff j e)) p =
      fderiv ℝ (fun p => unaryValue (Encodable.encode m) (value e p)) p _
    unfold diffUnary unaryValue
    split_ifs with h₀ h₁
    · simp
    · have hn := nonzero_of_inverse_bound (he.2 h₁ p)
      simp only [value, value_invE, ih he.1]
      have hd := ((hasDerivAt_inv hn).comp_hasFDerivAt p (he' p).hasFDerivAt).fderiv
      change fderiv ℝ (fun p => (value e p)⁻¹) p = _ at hd
      rw [hd]
      simp [pow_two, mul_assoc]
    · simp only [value, value_cst, Qval_nat, Rat.cast_natCast, value_flatE, ih he.1]
      have hd := ((hasDerivAt_flatTerm (Encodable.encode m / 3) (value e p)).comp_hasFDerivAt p (he' p).hasFDerivAt).fderiv
      change fderiv ℝ (fun p => flatTerm (Encodable.encode m / 3) (value e p)) p = _ at hd
      rw [hd]
      simp only [smul_apply, smul_eq_mul]
      ring

end BoxTransport.Routing.Computation

open scoped BigOperators ContDiff
open Nat.Partrec (Code)
namespace BoxTransport.Routing.Computation

def qGuardInv (b : ℕ) (q : QCode) : QCode :=
  if qLe (qInv (qNat (2 * (b + 1)))) (qAbs q) then qInv q else qZero

def unaryBound (m : ℕ) (_radius : ℕ) : ℕ :=
  if m % 3 = 0 then qBound (Denumerable.ofNat QCode (m / 3))
  else if m % 3 = 1 then m / 3 + 1 else (m / 3).factorial

def boundE (R : ℕ) : Expr → ℕ
  | .zero | .succ | .left | .right => R
  | .pair e f => boundE R e + boundE R f
  | .comp e f => boundE R e * boundE R f
  | .prec m _ => unaryBound (Encodable.encode m) R
  | .rfind' e => boundE R e

def unaryAmp (m A : ℕ) : ℕ :=
  if m % 3 = 0 then 0
  else if m % 3 = 1 then 2 * (m / 3 + 1) ^ 2 * A
  else flatLipschitzBound (m / 3) * A + 1

def ampE (R : ℕ) : Expr → ℕ
  | .zero | .succ | .left | .right => 0
  | .pair e f => ampE R e + ampE R f
  | .comp e f => (boundE R e + ampE R e) * ampE R f + boundE R f * ampE R e
  | .prec m e => unaryAmp (Encodable.encode m) (ampE R e)
  | .rfind' e => ampE R e

noncomputable def unaryEval (m : ℕ) (q : QCode) (N : ℕ) : QCode :=
  if m % 3 = 0 then Denumerable.ofNat QCode (m / 3)
  else if m % 3 = 1 then qGuardInv (m / 3) q else qFlat (m / 3, q, N)

noncomputable def evalE (q : RationalPointCode) (N : ℕ) : Expr → QCode
  | .zero => q.1
  | .succ => q.2.1
  | .left => q.2.2.1
  | .right => q.2.2.2
  | .pair e f => qAdd (evalE q N e) (evalE q N f)
  | .comp e f => qMul (evalE q N e) (evalE q N f)
  | .prec m e => unaryEval (Encodable.encode m) (evalE q N e) N
  | .rfind' e => qNeg (evalE q N e)

end BoxTransport.Routing.Computation

open scoped BigOperators ContDiff
open Nat.Partrec (Code)
namespace BoxTransport.Routing.Computation

attribute [fun_prop] Primrec Computable
attribute [fun_prop] Primrec.const Primrec.id Primrec.fst Primrec.snd Primrec.comp Primrec.pair Primrec.succ Primrec.encode Primrec.ofNat
attribute [fun_prop] Computable.const Computable.id Computable.fst Computable.snd Computable.comp Computable.pair

@[fun_prop] theorem pr_add {α} [Primcodable α] {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => f a + g a) := Primrec.nat_add.comp hf hg
@[fun_prop] theorem pr_mul {α} [Primcodable α] {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => f a * g a) := Primrec.nat_mul.comp hf hg
@[fun_prop] theorem pr_sub {α} [Primcodable α] {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => f a - g a) := Primrec.nat_sub.comp hf hg
@[fun_prop] theorem pr_div {α} [Primcodable α] {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => f a / g a) := Primrec.nat_div.comp hf hg
@[fun_prop] theorem pr_mod {α} [Primcodable α] {f g : α → ℕ} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => f a % g a) := Primrec.nat_mod.comp hf hg
@[fun_prop] theorem pr_square {α} [Primcodable α] {f : α → ℕ} (hf : Primrec f) :
    Primrec (fun a => f a ^ 2) := by simpa only [pow_two] using pr_mul hf hf
@[fun_prop] theorem pr_pair {α} [Primcodable α] {f g : α → Expr} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => Code.pair (f a) (g a)) := Code.primrec₂_pair.comp hf hg
@[fun_prop] theorem pr_comp {α} [Primcodable α] {f g : α → Expr} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => Code.comp (f a) (g a)) := Code.primrec₂_comp.comp hf hg
@[fun_prop] theorem pr_prec {α} [Primcodable α] {f g : α → Expr} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => Code.prec (f a) (g a)) := Code.primrec₂_prec.comp hf hg
attribute [fun_prop] Code.primrec_rfind' primrec_qNat primrec_qBound primrec_qInv primrec_qAbs primrec_qNeg primrec_factorial

@[fun_prop] theorem pr_qAdd {α} [Primcodable α] {f g : α → QCode} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => qAdd (f a) (g a)) := primrec_qAdd.comp hf hg
@[fun_prop] theorem pr_qMul {α} [Primcodable α] {f g : α → QCode} (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun a => qMul (f a) (g a)) := primrec_qMul.comp hf hg

@[fun_prop] theorem primrec_node : Primrec (fun p : ℕ × Expr => node p.1 p.2) := by
  unfold node; fun_prop
@[fun_prop] theorem pr_node {α} [Primcodable α] {m : α → ℕ} {e : α → Expr}
    (hm : Primrec m) (he : Primrec e) : Primrec (fun a => node (m a) (e a)) := primrec_node.comp (hm.pair he)
@[fun_prop] theorem primrec_cst : Primrec cst := by unfold cst; fun_prop
@[fun_prop] theorem pr_invE {α} [Primcodable α] {m : α → ℕ} {e : α → Expr}
    (hm : Primrec m) (he : Primrec e) : Primrec (fun a => invE (m a) (e a)) := by unfold invE; fun_prop
@[fun_prop] theorem pr_flatE {α} [Primcodable α] {m : α → ℕ} {e : α → Expr}
    (hm : Primrec m) (he : Primrec e) : Primrec (fun a => flatE (m a) (e a)) := by unfold flatE; fun_prop

@[fun_prop] theorem primrec_diffUnary :
    Primrec (fun p : ℕ × Expr × Expr => diffUnary p.1 p.2.1 p.2.2) := by
  unfold diffUnary
  apply Primrec.ite (Primrec.eq.comp (by fun_prop) (Primrec.const 0))
  · fun_prop
  apply Primrec.ite (Primrec.eq.comp (by fun_prop) (Primrec.const 1)) <;> fun_prop

theorem diff_eq_rec (j : Axis) (e : Expr) : diff j e =
    Code.recOn e (cst (if j = none then qOne else qZero))
      (cst (if j = some 0 then qOne else qZero))
      (cst (if j = some 1 then qOne else qZero))
      (cst (if j = some 2 then qOne else qZero))
      (fun _ _ de df => Code.pair de df)
      (fun e f de df => Code.pair (Code.comp de f) (Code.comp e df))
      (fun m e _ de => diffUnary (Encodable.encode m) e de)
      (fun _ de => Code.rfind' de) := by
  induction e <;> simp_all only [diff]

@[fun_prop] theorem primrec_diff : Primrec (fun p : Axis × Expr => diff p.1 p.2) := by
  simp_rw [diff_eq_rec]
  apply Code.primrec_recOn Primrec.snd
  · exact (show Primrec (fun j : Axis => cst (if j = none then qOne else qZero)) from Primrec.dom_finite _).comp Primrec.fst
  · exact (show Primrec (fun j : Axis => cst (if j = some 0 then qOne else qZero)) from Primrec.dom_finite _).comp Primrec.fst
  · exact (show Primrec (fun j : Axis => cst (if j = some 1 then qOne else qZero)) from Primrec.dom_finite _).comp Primrec.fst
  · exact (show Primrec (fun j : Axis => cst (if j = some 2 then qOne else qZero)) from Primrec.dom_finite _).comp Primrec.fst
  · fun_prop
  · fun_prop
  · fun_prop
  · fun_prop

@[fun_prop] theorem primrec_unaryBound : Primrec (fun p : ℕ × ℕ => unaryBound p.1 p.2) := by
  unfold unaryBound
  apply Primrec.ite (Primrec.eq.comp (by fun_prop) (Primrec.const 0))
  · fun_prop
  apply Primrec.ite (Primrec.eq.comp (by fun_prop) (Primrec.const 1)) <;> fun_prop

theorem boundE_eq_rec (R : ℕ) (e : Expr) : boundE R e =
    Code.recOn e R R R R (fun _ _ a b => a + b) (fun _ _ a b => a * b)
      (fun m _ _ _ => unaryBound (Encodable.encode m) R) (fun _ a => a) := by
  induction e <;> simp_all only [boundE]

@[fun_prop] theorem primrec_boundE : Primrec (fun p : ℕ × Expr => boundE p.1 p.2) := by
  simp_rw [boundE_eq_rec]
  apply Code.primrec_recOn Primrec.snd <;> fun_prop

@[fun_prop] theorem primrec_unaryAmp : Primrec (fun p : ℕ × ℕ => unaryAmp p.1 p.2) := by
  unfold unaryAmp flatLipschitzBound
  apply Primrec.ite (Primrec.eq.comp (by fun_prop) (Primrec.const 0))
  · fun_prop
  apply Primrec.ite (Primrec.eq.comp (by fun_prop) (Primrec.const 1)) <;> fun_prop

theorem ampE_eq_rec (R : ℕ) (e : Expr) : ampE R e =
    Code.recOn e 0 0 0 0 (fun _ _ a b => a + b)
      (fun e f a b => (boundE R e + a) * b + boundE R f * a)
      (fun m _ _ a => unaryAmp (Encodable.encode m) a) (fun _ a => a) := by
  induction e <;> simp_all only [ampE]

@[fun_prop] theorem primrec_ampE : Primrec (fun p : ℕ × Expr => ampE p.1 p.2) := by
  simp_rw [ampE_eq_rec]
  apply Code.primrec_recOn Primrec.snd <;> fun_prop

@[fun_prop] theorem primrec_qGuardInv : Primrec (fun p : ℕ × QCode => qGuardInv p.1 p.2) := by
  unfold qGuardInv
  apply Primrec.ite (primrec_qLe.comp (by fun_prop) (by fun_prop)) <;> fun_prop

attribute [fun_prop] Primrec.to_comp computable_qFlat

@[fun_prop] theorem computable_unaryEval :
    Computable (fun p : ℕ × QCode × ℕ => unaryEval p.1 p.2.1 p.2.2) := by
  unfold unaryEval
  apply computable_ite (PrimrecPred.computablePred (Primrec.eq.comp (by fun_prop) (Primrec.const 0)))
  · fun_prop
  apply computable_ite (PrimrecPred.computablePred (Primrec.eq.comp (by fun_prop) (Primrec.const 1))) <;> fun_prop

theorem evalE_eq_rec (q : RationalPointCode) (N : ℕ) (e : Expr) : evalE q N e =
    Code.recOn e q.1 q.2.1 q.2.2.1 q.2.2.2
      (fun _ _ a b => qAdd a b) (fun _ _ a b => qMul a b)
      (fun m _ _ a => unaryEval (Encodable.encode m) a N) (fun _ a => qNeg a) := by
  induction e <;> simp_all only [evalE]

theorem computable_Expr_recOn {α σ}
    [Primcodable α] [Primcodable σ] {c : α → Code} (hc : Computable c) {z : α → σ}
    (hz : Computable z) {s : α → σ} (hs : Computable s) {l : α → σ} (hl : Computable l) {r : α → σ}
    (hr : Computable r) {pr : α → Code → Code → σ → σ → σ}
    (hpr : Computable fun a : α × Code × Code × σ × σ => pr a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)
    {co : α → Code → Code → σ → σ → σ}
    (hco : Computable fun a : α × Code × Code × σ × σ => co a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)
    {pc : α → Code → Code → σ → σ → σ}
    (hpc : Computable fun a : α × Code × Code × σ × σ => pc a.1 a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2)
    {rf : α → Code → σ → σ} (hrf : Computable fun a : α × Code × σ => rf a.1 a.2.1 a.2.2) :
    Computable (fun a : α => (Code.recOn (c a) (z a) (s a) (l a) (r a) (pr a) (co a) (pc a) (rf a) : σ)) :=
  Code.computable_recOn hc hz hs hl hr
    (pr := fun a b => pr a b.1 b.2.1 b.2.2.1 b.2.2.2) (.mk hpr)
    (co := fun a b => co a b.1 b.2.1 b.2.2.1 b.2.2.2) (.mk hco)
    (pc := fun a b => pc a b.1 b.2.1 b.2.2.1 b.2.2.2) (.mk hpc)
    (rf := fun a b => rf a b.1 b.2) (.mk hrf)

@[fun_prop] theorem computable_evalE :
    Computable (fun p : RationalPointCode × ℕ × Expr => evalE p.1 p.2.1 p.2.2) := by
  simp_rw [evalE_eq_rec]
  apply computable_Expr_recOn (Computable.snd.comp Computable.snd) <;> fun_prop

end BoxTransport.Routing.Computation

open scoped BigOperators ContDiff
open Nat.Partrec (Code)
namespace BoxTransport.Routing.Computation

def pointBound (q : RationalPointCode) : ℕ :=
  qBound q.1 + qBound q.2.1 + qBound q.2.2.1 + qBound q.2.2.2

@[fun_prop] theorem primrec_pointBound : Primrec pointBound := by unfold pointBound; fun_prop

noncomputable def evalPrecise (e : Expr) (q : RationalPointCode) (N : ℕ) : QCode :=
  evalE q ((N + 1) * (ampE (pointBound q) e + 1)) e

@[fun_prop] theorem computable_evalPrecise :
    Computable (fun p : Expr × RationalPointCode × ℕ => evalPrecise p.1 p.2.1 p.2.2) := by
  unfold evalPrecise
  fun_prop

def mixedE (ds : List Axis) (e : Expr) : Expr := ds.foldr diff e

@[simp] theorem mixedE_nil (e : Expr) : mixedE [] e = e := rfl
@[simp] theorem mixedE_cons (j : Axis) (ds : List Axis) (e : Expr) :
    mixedE (j :: ds) e = diff j (mixedE ds e) := rfl

@[fun_prop] theorem primrec_mixedE : Primrec (fun p : List Axis × Expr => mixedE p.1 p.2) := by
  unfold mixedE
  exact Primrec.list_foldr (h := fun _ p => diff p.1 p.2) Primrec.fst Primrec.snd (.mk (primrec_diff.comp Primrec.snd))

def familyBound (R : ℕ) (es : Fin 3 → Expr) (ds : List Axis) : ℕ :=
  boundE R (mixedE ds (es 0)) + boundE R (mixedE ds (es 1)) + boundE R (mixedE ds (es 2))

@[fun_prop] theorem primrec_familyBound (R : ℕ) (es : Fin 3 → Expr) :
    Primrec (familyBound R es) := by unfold familyBound; fun_prop

def gradientBound (R : ℕ) (es : Fin 3 → Expr) (ds : List Axis) : ℕ :=
  familyBound R es (none :: ds) + familyBound R es (some 0 :: ds) +
    familyBound R es (some 1 :: ds) + familyBound R es (some 2 :: ds)

@[fun_prop] theorem pr_list_cons {α β} [Primcodable α] [Primcodable β] {f : α → β} {g : α → List β}
    (hf : Primrec f) (hg : Primrec g) : Primrec (fun a => f a :: g a) := Primrec.list_cons.comp hf hg

@[fun_prop] theorem primrec_gradientBound (R : ℕ) (es : Fin 3 → Expr) :
    Primrec (gradientBound R es) := by unfold gradientBound; fun_prop

end BoxTransport.Routing.Computation

open scoped BigOperators ContDiff
open Nat.Partrec (Code)
namespace BoxTransport.Routing.Computation

def Representable (f : SpaceTime → ℝ) : Prop := ∃ e : Expr, Valid e ∧ value e = f

attribute [fun_prop] Representable

namespace Representable

@[fun_prop] theorem rational (q : ℚ) : Representable (fun _ => (q : ℝ)) := by
  obtain ⟨r, hr⟩ := Qval_surjective q
  exact ⟨cst r, valid_cst r, by funext p; simp [hr]⟩

@[fun_prop] theorem nat (n : ℕ) : Representable (fun _ => (n : ℝ)) := by
  simpa using rational (n : ℚ)

@[fun_prop] theorem ofNat (n : ℕ) [n.AtLeastTwo] : Representable (fun _ => (ofNat(n) : ℝ)) := nat n

@[fun_prop] theorem zero : Representable (fun _ => (0 : ℝ)) := by simpa using nat 0
@[fun_prop] theorem one : Representable (fun _ => (1 : ℝ)) := by simpa using nat 1
@[fun_prop] theorem time : Representable (fun p : SpaceTime => p.1) :=
  ⟨.zero, trivial, rfl⟩
@[fun_prop] theorem space (j : Fin 3) : Representable (fun p : SpaceTime => p.2 j) :=
  ⟨varE (some j), valid_varE _, by funext p; simp⟩

@[fun_prop] theorem add {f g : SpaceTime → ℝ} (hf : Representable f) (hg : Representable g) :
    Representable (fun p => f p + g p) := by
  obtain ⟨e, he, rfl⟩ := hf
  obtain ⟨d, hd, rfl⟩ := hg
  exact ⟨.pair e d, ⟨he, hd⟩, rfl⟩

@[fun_prop] theorem mul {f g : SpaceTime → ℝ} (hf : Representable f) (hg : Representable g) :
    Representable (fun p => f p * g p) := by
  obtain ⟨e, he, rfl⟩ := hf
  obtain ⟨d, hd, rfl⟩ := hg
  exact ⟨.comp e d, ⟨he, hd⟩, rfl⟩

@[fun_prop] theorem neg {f : SpaceTime → ℝ} (hf : Representable f) :
    Representable (fun p => -f p) := by
  obtain ⟨e, he, rfl⟩ := hf
  exact ⟨.rfind' e, he, rfl⟩

@[fun_prop] theorem sub {f g : SpaceTime → ℝ} (hf : Representable f) (hg : Representable g) :
    Representable (fun p => f p - g p) := by simpa only [sub_eq_add_neg] using hf.add hg.neg

@[fun_prop] theorem div_rat {f : SpaceTime → ℝ} (hf : Representable f) (q : ℚ) :
    Representable (fun p => f p / (q : ℝ)) := by
  simpa only [Rat.cast_inv, div_eq_mul_inv] using hf.mul (rational q⁻¹)

@[fun_prop] theorem div_nat {f : SpaceTime → ℝ} (hf : Representable f) (n : ℕ) :
    Representable (fun p => f p / (n : ℝ)) := by simpa using hf.div_rat (n : ℚ)

@[fun_prop] theorem div_ofNat {f : SpaceTime → ℝ} (hf : Representable f) (n : ℕ) [n.AtLeastTwo] :
    Representable (fun p => f p / (ofNat(n) : ℝ)) := hf.div_nat n

@[fun_prop] theorem flat {f : SpaceTime → ℝ} (hf : Representable f) (m : ℕ) :
    Representable (fun p => flatTerm m (f p)) := by
  obtain ⟨e, he, rfl⟩ := hf
  exact ⟨flatE m e, (valid_flatE _ _).2 he, by funext p; simp⟩

@[fun_prop] theorem glue {f : SpaceTime → ℝ} (hf : Representable f) :
    Representable (fun p => expNegInvGlue (f p)) := by
  simpa only [flatTerm, pow_zero, one_mul] using hf.flat 0

lemma exists_inv_nat_le {ε : ℝ} (hε : 0 < ε) : ∃ b : ℕ, ((b : ℝ) + 1)⁻¹ ≤ ε := by
  obtain ⟨b, hb⟩ := exists_nat_gt ε⁻¹
  refine ⟨b, (inv_le_iff_one_le_mul₀ (by positivity)).2 ?_⟩
  have h := mul_lt_mul_of_pos_left hb hε
  rw [mul_inv_cancel₀ (ne_of_gt hε)] at h
  nlinarith

theorem inv {f : SpaceTime → ℝ} (hf : Representable f)
    (hsep : ∃ ε : ℝ, 0 < ε ∧ ∀ p, ε ≤ |f p|) : Representable (fun p => (f p)⁻¹) := by
  obtain ⟨e, he, rfl⟩ := hf
  obtain ⟨ε, hε, hsep⟩ := hsep
  obtain ⟨b, hb⟩ := exists_inv_nat_le hε
  exact ⟨invE b e, (valid_invE _ _).2 ⟨he, fun p => hb.trans (hsep p)⟩,
    by funext p; simp⟩

theorem div {f g : SpaceTime → ℝ} (hf : Representable f) (hg : Representable g)
    (hsep : ∃ ε : ℝ, 0 < ε ∧ ∀ p, ε ≤ |g p|) : Representable (fun p => f p / g p) := by
  simpa only [div_eq_mul_inv] using hf.mul (hg.inv hsep)

theorem transition_denom_lower (x : ℝ) :
    expNegInvGlue (1 / 2) ≤ expNegInvGlue x + expNegInvGlue (1 - x) := by
  rcases le_total (1 / 2 : ℝ) x with hx | hx
  · exact (expNegInvGlue.monotone hx).trans (le_add_of_nonneg_right (expNegInvGlue.nonneg _))
  · have hy : (1 / 2 : ℝ) ≤ 1 - x := by linarith
    exact (expNegInvGlue.monotone hy).trans (le_add_of_nonneg_left (expNegInvGlue.nonneg _))

@[fun_prop] theorem transition {f : SpaceTime → ℝ} (hf : Representable f) :
    Representable (fun p => Real.smoothTransition (f p)) := by
  apply hf.glue.div (hf.glue.add ((one.sub hf).glue))
  refine ⟨expNegInvGlue (1 / 2), expNegInvGlue.pos_of_pos (by norm_num), fun p => ?_⟩
  rw [abs_of_nonneg (add_nonneg (expNegInvGlue.nonneg _) (expNegInvGlue.nonneg _))]
  exact transition_denom_lower _

@[fun_prop] theorem directional {f : SpaceTime → ℝ} (hf : Representable f) (j : Axis) :
    Representable (fun p => fderiv ℝ f p (coordinateDirection j)) := by
  obtain ⟨e, he, rfl⟩ := hf
  exact ⟨diff j e, valid_diff he j, funext (value_diff he j)⟩

theorem smooth {f : SpaceTime → ℝ} (hf : Representable f) : ContDiff ℝ ∞ f := by
  obtain ⟨e, he, rfl⟩ := hf
  exact smooth_value he

@[fun_prop] theorem sum {ι : Type*} (s : Finset ι) {f : ι → SpaceTime → ℝ}
    (hf : ∀ i ∈ s, Representable (f i)) : Representable (fun p => ∑ i ∈ s, f i p) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using zero
  | @insert i s hi ih =>
    simpa only [Finset.sum_insert hi] using (hf i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

@[fun_prop] theorem prod {ι : Type*} (s : Finset ι) {f : ι → SpaceTime → ℝ}
    (hf : ∀ i ∈ s, Representable (f i)) : Representable (fun p => ∏ i ∈ s, f i p) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using one
  | @insert i s hi ih =>
    simpa only [Finset.prod_insert hi] using (hf i (Finset.mem_insert_self _ _)).mul
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

end Representable

end BoxTransport.Routing.Computation

end

end OAI


