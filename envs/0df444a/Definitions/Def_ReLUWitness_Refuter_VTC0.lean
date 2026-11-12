-- Prove2me | Definitions.Def_ReLUWitness_Refuter_VTC0
-- name    : ReLUWitness_Refuter_VTC0
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-11T06:50:23.98346+00:00
-- url     : https://prove2.me/theorems/d6c45762-368f-46f7-9a6a-ba309eba1b6a
-- title:
--   The theory VTC⁰ (2-BASIC, Σ^B_0 comprehension, counting axiom) and its extension T by chosen FTC⁰ functions; provability as truth in all models
-- statement:
--   **2-BASIC** is the axiom list of [CN10, Figure 2]: $x+1\ne0$; $x+1=y+1\to x=y$; $x+0=x$; $x+(y+1)=(x+y)+1$; $x\cdot0=0$; $x\cdot(y+1)=x\cdot y+x$; $x\le y\wedge y\le x\to x=y$; $x\le x+y$; $0\le x$; $x\le y\vee y\le x$; $x\le y\leftrightarrow x<y+1$; $x\ne0\to\exists y\le x\,(y+1=x)$; $X(y)\to y<|X|$; $y+1=|X|\to X(y)$; and string extensionality $|X|=|Y|\wedge\forall i<|X|\,(X(i)\leftrightarrow Y(i))\to X=Y$.
--
--   **$\Sigma^B_0$ comprehension** asserts, for every $\Sigma^B_0$ formula $\varphi(z)$ (with parameters) and bound $b$, a string with no bits at or above $b$ whose bit $z<b$ holds exactly when $\varphi(z)$ does. The **counting axiom** of $\mathbf{VTC}^0$, in the bounded form of Lemma 2.4, is
--
--   $$\forall X\,\forall y\,\exists Z\le 1+\langle y,y\rangle\ \delta_{\mathrm{NUM}}(y,X,Z),$$
--
--   where $(Z)_u$ is the least $w<|Z|$ with $Z(\langle u,w\rangle)$ (or $|Z|$) and $\delta_{\mathrm{NUM}}$ says $(Z)_0=0$ and, for $u<y$, $(Z)_{u+1}=(Z)_u+1$ if $X(u)$ and $(Z)_{u+1}=(Z)_u$ otherwise.
--
--   **The extension.** For a program $P$ of chosen definitions, a **model of $T(P)$** is a structure satisfying 2-BASIC, $\Sigma^B_0$ comprehension for every $\Sigma^B_0$ formula of the language extended by the primitives and the symbols of $P$, the counting axiom, the defining axioms of the primitives, and the defining axioms of $P$ (the bit-definition and minimization equations). The primitives' axioms are their bit-definitions (rows: $X[a](i)\leftrightarrow i<|X|\wedge X(\langle a,i\rangle)$; binary addition by the carry formula $\exists k<i\,(X(k)\wedge Y(k)\wedge\forall j<i\,(k<j\to X(j)\vee Y(j)))$; cut, shift, empty string, magnitude, sign) and the recurrence equations of the imported threshold functions: $\mathrm{numones}(0,X)=0$ and $\mathrm{numones}(y+1,X)=\mathrm{numones}(y,X)+[X(y)]$; $\mathrm{isum}(0,X)=\emptyset$, $\mathrm{isum}(b+1,X)=\mathrm{isum}(b,X)+X[b]$; multiplication by shift-and-add over the bits of the second factor; interval products with empty product one and $\mathrm{imul}(i,j+1,X)=\mathrm{imul}(i,j,X)\cdot X[j]$; $Y\le_2X\to Y+(X-Y)=X$; and $A=B\cdot Q+R$, $R<_2B$ for a positive divisor $B$.
--
--   **Provability.** "$T(P)$ proves $\varphi$" is encoded as: $\varphi$ holds in every model of $T(P)$ (equivalent to derivability by the completeness theorem).
--
--   **Formalization Note.** The paper's $T$ is the universal conservative extension of $\mathbf{VTC}^0$ by all chosen $\mathrm{FTC}^0$ functions (Fact 8.1). A sentence about finitely many symbols is encoded with the program $P$ that defines them. $T$ proves every axiom of $T(P)$: comprehension for $\Sigma^B_0$ formulas of its language [CN10, Theorem 9.34(c)] and the imported equations (Fact 2.3, Fact 8.1). So a theorem of $T(P)$ is a theorem of $T$.
-- source:
--   Myrisiotis, A Witnessing Duality for ReLU Network Depth, arXiv:2610.38281v1, pp. 12, 14-15 (2-BASIC, V⁰, VTC⁰, Lemma 2.4's counting axiom); pp. 46-47, §8 and Fact 8.1 (the extension T)

import Mathlib
import Definitions.Def_ReLUWitness_Refuter_TwoSorted

open scoped Classical

namespace ReLUWitness.Refuter

/-! The theory VTC⁰ (2-BASIC, Σ^B_0 comprehension, the counting axiom) and its
conservative extension `T` by chosen FTC⁰ function symbols, with provability encoded as
truth in every two-sorted model (Myrisiotis, arXiv:2610.38281v1, pp. 12-15 and p. 46). -/

namespace Structure

variable (M : Structure)

/-- The axioms 2-BASIC of [CN10, Figure 2]: B1-B12, L1, L2 and string extensionality SE. -/
def Basic2 : Prop :=
  (∀ x, M.add x M.one ≠ M.zero) ∧
  (∀ x y, M.add x M.one = M.add y M.one → x = y) ∧
  (∀ x, M.add x M.zero = x) ∧
  (∀ x y, M.add x (M.add y M.one) = M.add (M.add x y) M.one) ∧
  (∀ x, M.mul x M.zero = M.zero) ∧
  (∀ x y, M.mul x (M.add y M.one) = M.add (M.mul x y) x) ∧
  (∀ x y, M.le x y → M.le y x → x = y) ∧
  (∀ x y, M.le x (M.add x y)) ∧
  (∀ x, M.le M.zero x) ∧
  (∀ x y, M.le x y ∨ M.le y x) ∧
  (∀ x y, M.le x y ↔ M.lt x (M.add y M.one)) ∧
  (∀ x, x ≠ M.zero → ∃ y, M.le y x ∧ M.add y M.one = x) ∧
  (∀ (X : M.S) y, M.mem y X → M.lt y (M.len X)) ∧
  (∀ (X : M.S) y, M.add y M.one = M.len X → M.mem y X) ∧
  (∀ X Y : M.S, M.len X = M.len Y → (∀ i, M.lt i (M.len X) → (M.mem i X ↔ M.mem i Y)) → X = Y)

/-- `(Z)_u = w`: the least `w < |Z|` with `Z(⟨u,w⟩)`, or `|Z|` if there is none
([CN10, Definition 5.56], p. 15). -/
def IsEnt (Z : M.S) (u w : M.N) : Prop :=
  (M.lt w (M.len Z) ∧ M.mem (M.pair u w) Z ∧ ∀ v, M.lt v w → ¬ M.mem (M.pair u v) Z) ∨
  (w = M.len Z ∧ ∀ v, M.lt v (M.len Z) → ¬ M.mem (M.pair u v) Z)

/-- `δ_NUM(y, X, Z)` of Lemma 2.4 (p. 15). -/
def DeltaNum (y : M.N) (X Z : M.S) : Prop :=
  M.IsEnt Z M.zero M.zero ∧
  ∀ u, M.lt u y → ∀ w, M.IsEnt Z u w →
    (M.mem u X → M.IsEnt Z (M.add u M.one) (M.add w M.one)) ∧
    (¬ M.mem u X → M.IsEnt Z (M.add u M.one) w)

/-- The counting axiom of VTC⁰ in its bounded form `∀X ∀y ∃Z ≤ 1+⟨y,y⟩ δ_NUM(y,X,Z)`. -/
def Counting : Prop :=
  ∀ (X : M.S) (y : M.N), ∃ Z : M.S,
    M.le (M.len Z) (M.add M.one (M.pair y y)) ∧ M.DeltaNum y X Z

/-- Carry bit of binary addition, `∃k<i (X(k) ∧ Y(k) ∧ ∀j<i (k<j → X(j) ∨ Y(j)))`. -/
def Carry (i : M.N) (X Y : M.S) : Prop :=
  ∃ k, M.lt k i ∧ M.mem k X ∧ M.mem k Y ∧ ∀ j, M.lt j i → M.lt k j → (M.mem j X ∨ M.mem j Y)

/-- Defining axioms of the primitive symbols: bit-definitions for the AC⁰ ones
(row, empty string, binary addition, cut, shift, magnitude, sign recoding) and the
recurrence/specification equations of the imported threshold functions (counting,
iterated addition, multiplication, interval products with empty product one,
truncated subtraction, division with remainder): Fact 2.3, Fact 8.1, pp. 14, 46-47. -/
def PrimAx : Prop :=
  -- counting function
  (∀ X : M.S, M.numones M.zero X = M.zero ∧
    ∀ y, (M.mem y X → M.numones (M.add y M.one) X = M.add (M.numones y X) M.one) ∧
         (¬ M.mem y X → M.numones (M.add y M.one) X = M.numones y X)) ∧
  -- rows of arrays: `X[a](i) ↔ i < |X| ∧ X(⟨a,i⟩)`
  (∀ a (X : M.S) i, M.mem i (M.row a X) ↔ M.lt i (M.len X) ∧ M.mem (M.pair a i) X) ∧
  -- the empty string
  (∀ i, ¬ M.mem i M.empt) ∧
  -- binary addition (carry-lookahead bit definition)
  (∀ (X Y : M.S) i, M.mem i (M.badd X Y) ↔
      M.lt i (M.add (M.len X) (M.len Y)) ∧
      (M.mem i X ↔ (M.mem i Y ↔ M.Carry i X Y))) ∧
  -- truncated subtraction: `Y ≤ X → Y + (X - Y) = X`, and `X - Y = ∅` otherwise
  (∀ X Y : M.S, (M.BLe Y X → M.badd Y (M.bsub X Y) = X) ∧
      (¬ M.BLe Y X → M.bsub X Y = M.empt)) ∧
  -- cut: the bits below `b`
  (∀ b (X : M.S) i, M.mem i (M.cut b X) ↔ M.lt i b ∧ M.mem i X) ∧
  -- shift left by `k`
  (∀ k (X : M.S) i, M.mem i (M.shl k X) ↔ ∃ j, M.add j k = i ∧ M.mem j X) ∧
  -- iterated addition of rows `0, …, b-1`
  (∀ X : M.S, M.isum M.zero X = M.empt ∧
    ∀ b, M.isum (M.add b M.one) X = M.badd (M.isum b X) (M.row b X)) ∧
  -- binary multiplication by shift-and-add over the bits of the second factor
  (∀ X Y : M.S, M.bmul X (M.cut M.zero Y) = M.empt ∧
    ∀ b, M.bmul X (M.cut (M.add b M.one) Y) =
      M.badd (M.bmul X (M.cut b Y)) (if M.mem b Y then M.shl b X else M.empt)) ∧
  -- interval products of rows `i, …, j-1`, empty product one
  (∀ i j (X : M.S), (M.le j i → ∀ z, M.mem z (M.imul i j X) ↔ z = M.zero) ∧
    (M.le i j → M.imul i (M.add j M.one) X = M.bmul (M.imul i j X) (M.row j X))) ∧
  -- division with remainder by a positive divisor
  (∀ A B : M.S, (M.lt M.zero (M.len B) →
      A = M.badd (M.bmul B (M.bdiv A B)) (M.bmod A B) ∧ M.BLt (M.bmod A B) B) ∧
    (M.len B = M.zero → M.bdiv A B = M.empt ∧ M.bmod A B = M.empt)) ∧
  -- magnitude of a signed code: bit `i` is bit `i+1` of the code
  (∀ (u : M.S) i, M.mem i (M.mag u) ↔ M.mem (M.add i M.one) u) ∧
  -- signed code from a sign number `s` and a magnitude `X` (sign bit only if `s = 1`, `X ≠ ∅`)
  (∀ s (X : M.S) z, M.mem z (M.sgnd s X) ↔
      (z = M.zero ∧ s = M.one ∧ ∃ i, M.mem i X) ∨ (∃ i, z = M.add i M.one ∧ M.mem i X))

/-- Σ^B_0 comprehension for every Σ^B_0 formula of the language of `P`
(with arbitrary parameters): there is a string with no bits at or above `b` whose bit `z`,
for `z < b`, holds exactly when `φ(z)` holds. -/
def Comp (P : Program) : Prop :=
  ∀ φ : Fml, φ.isSigmaB0 = true → φ.ok (P.symSig P.length) (fun _ => true) (fun _ => true) = true →
    ∀ (ρ : Assignment M) (v : ℕ) (b : M.N), ∃ X : M.S,
      (∀ z, M.mem z X → M.lt z b) ∧
      ∀ z, M.lt z b → (M.mem z X ↔ φ.Sat M (ρ.setN v z))

/-- The argument lists `(x₁,…,x_nn)`, `(X₀,…,X_{ns-1})` read off an assignment. -/
def argsN (ρ : Assignment M) (nn : ℕ) : List M.N := (List.range nn).map (fun j => ρ.n (j + 1))
def argsS (ρ : Assignment M) (ns : ℕ) : List M.S := (List.range ns).map ρ.s

/-- The defining axioms of the chosen definitions of `P`. -/
def DefAx (P : Program) : Prop :=
  ∀ k (h : k < P.length) (ρ : Assignment M),
    match P[k]'h with
    | .bit nn ns t φ =>
        ∀ i, M.mem i (M.sfun (.defd k) (M.argsN ρ nn) (M.argsS ρ ns)) ↔
          (M.lt i (t.eval M ρ) ∧ φ.Sat M (ρ.setN 0 i))
    | .min nn ns t φ =>
        (M.nfun (.defd k) (M.argsN ρ nn) (M.argsS ρ ns) = t.eval M ρ ∧
          ∀ y, M.lt y (t.eval M ρ) → ¬ φ.Sat M (ρ.setN 0 y)) ∨
        (M.lt (M.nfun (.defd k) (M.argsN ρ nn) (M.argsS ρ ns)) (t.eval M ρ) ∧
          φ.Sat M (ρ.setN 0 (M.nfun (.defd k) (M.argsN ρ nn) (M.argsS ρ ns))) ∧
          ∀ y, M.lt y (M.nfun (.defd k) (M.argsN ρ nn) (M.argsS ρ ns)) → ¬ φ.Sat M (ρ.setN 0 y))

/-- `M` is a model of `T(P)`: VTC⁰ (2-BASIC, Σ^B_0 comprehension, counting) in the language
extended by the primitives and the definitions of `P`, with their defining axioms. -/
def ModelT (P : Program) : Prop :=
  M.Basic2 ∧ M.Comp P ∧ M.Counting ∧ M.PrimAx ∧ M.DefAx P

end Structure

/-- `T(P) ⊢ φ`, encoded as truth of `φ` in every two-sorted model of `T(P)`
(equivalent to derivability by the completeness theorem). -/
def Proves (P : Program) (φ : Structure → Prop) : Prop :=
  ∀ M : Structure, M.ModelT P → φ M

end ReLUWitness.Refuter


