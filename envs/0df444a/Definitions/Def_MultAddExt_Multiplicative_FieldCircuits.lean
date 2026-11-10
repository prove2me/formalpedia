-- Prove2me | Definitions.Def_MultAddExt_Multiplicative_FieldCircuits
-- name    : MultAddExt_Multiplicative_FieldCircuits
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T01:47:57.66148+00:00
-- url     : https://prove2.me/theorems/9ed7e5da-69e0-4ba0-a0df-90f5ea115bb8
-- title:
--   Lines over F_q^d, circuits on field elements, and the line test of Lemma 8.2 (Definition 4.35)
-- statement:
--   Let $\mathbb F$ be a finite field with $q$ elements.
--
--   1. (Definition 4.35) The **parametrized line** through $u,v\in\mathbb F^d$ is $L(t)=u+t(v-u)$; it is **degenerate** if $u=v$. The experiment $L\leftarrow\mathrm{RandLine}$ draws $u,v$ independently and uniformly from $\mathbb F^d$; $\Pr_{L\leftarrow\mathrm{RandLine}}[E(L)]$ is the fraction of pairs $(u,v)$ with $E$.
--   2. For $q=2^\kappa$, $\mathbb F$ is a $\kappa$-dimensional vector space over $\mathbb F_2$; given a basis $B$, an element is written in binary by its $\kappa$ coordinates, and a point of $\mathbb F^d$ by the concatenation of its $d$ coordinates ($d\kappa$ bits). Circuits on field elements read and write these encodings; $\mathrm{ACCEPT}_C(x)\subseteq\mathbb F$ is the set of field elements whose encoding is an accepted output of $C$ on the encoding of $x$.
--   3. (Lemma 8.2) For a nondeterministic circuit $\mathrm{Thr}(w,a)$ with $w\in\mathbb F^d$, $a\in\mathbb F$, the **line test** of a function $\varphi:\mathbb F\to\mathbb F$ along $L$ is
--   $$\mathrm{Test}_L(\varphi)=\Pr_{t\leftarrow\mathbb F}\bigl[\mathrm{Thr}(L(t),\varphi(t))=1\bigr]$$
--   for nondegenerate $L$, and $0$ for degenerate $L$. For a polynomial $p\in\mathbb F[t]$, $\mathrm{Test}_L(p)$ is the test of $t\mapsto p(t)$.
--
--   These are the objects of the reconstruction step (Lemmas 8.2, 8.5) and the sampling lemma 4.37.
--
--   **Formalization Note** A field of order $2^\kappa$ is any finite field with an $\mathbb F_2$-algebra structure and a basis indexed by $\{0,\dots,\kappa-1\}$; every finite field of order $2^\kappa$ is of this form, and the statements quantify over every basis.
--
--   For Lemma 8.5, arbitrary finite fields are represented by a basis over their prime field ZMod p. Each basis coefficient is the canonical residue in [0,p), written in Nat.size p binary digits, least significant bit first. The total length L = κ·Nat.size p satisfies log₂ q ≤ L ≤ 2 log₂ q. primeVecBits concatenates these codes. Equality of the raw accepted-bit set to the singleton code enforces both correctness and absence of invalid accepted output codes.
-- source:
--   Ball, Chattopadhyay, Gurumukhani, Shaltiel, Zhao, Multiplicative and Additive Extractors for Low Entropy Samplable Sources Under Reduced Assumptions, STOC 2027 submission (manuscript sha256 5ac077d7…), Definition 4.35, p. 25 (PDF 29); Lemma 8.2, p. 46 (PDF 50); Definition 4.9, p. 19 (PDF 23)

import Mathlib
import Definitions.Def_MultAddExt_Multiplicative_FinDist
import Definitions.Def_MultAddExt_Multiplicative_NondetCircuit

set_option autoImplicit false

namespace MultAddExt.Multiplicative

/-! # Lines over `F_q^d`, circuits on field elements, and the line test (Definition 4.35, §8.2)

Ball, Chattopadhyay, Gurumukhani, Shaltiel, Zhao, *Multiplicative and Additive Extractors for Low
Entropy Samplable Sources Under Reduced Assumptions*, STOC 2027 submission (manuscript sha256
5ac077d7…), Definition 4.35, p. 25 (PDF 29); Lemma 8.2, p. 46 (PDF 50).

A field of order `q = 2^κ` is a finite field `F` with a basis `B` of `F` over `F₂ = ZMod 2`; an
element is written in binary by its `κ` coordinates in `B`. -/

/-- The parametrized line `L(t) = u + t(v − u)` through `u, v ∈ F^d` (Definition 4.35). -/
def line {F : Type*} [Field F] {d : ℕ} (u v : Fin d → F) (t : F) : Fin d → F :=
  u + t • (v - u)

/-- `Pr_{L ← RandLine}[E(L)]`: `u, v` independent and uniform on `F^d`, `L = line u v`. -/
noncomputable def randLineProb {F : Type*} [Fintype F] [Field F] {d : ℕ}
    (E : (Fin d → F) → (Fin d → F) → Prop) : ℝ :=
  probEvent (uniform ((Fin d → F) × (Fin d → F))) {uv | E uv.1 uv.2}

/-- The binary encoding of a field element: its `κ` coordinates over `F₂` in the basis `B`. -/
noncomputable def fieldBits {F : Type*} [Field F] [Algebra (ZMod 2) F] {κ : ℕ}
    (B : Module.Basis (Fin κ) (ZMod 2) F) (a : F) : Fin κ → Bool :=
  fun j => decide (B.repr a j = 1)

/-- The binary encoding of a point of `F^d`: the encodings of its `d` coordinates, concatenated. -/
noncomputable def vecBits {F : Type*} [Field F] [Algebra (ZMod 2) F] {κ d : ℕ}
    (B : Module.Basis (Fin κ) (ZMod 2) F) (x : Fin d → F) : Fin (d * κ) → Bool :=
  fun i => fieldBits B (x (finProdFinEquiv.symm i).1) (finProdFinEquiv.symm i).2

/-- `ACCEPT_C(x) ⊆ F` for a multi-output nondeterministic circuit `C` with input `x ∈ F^d` and
output in `F`, both in the binary encoding of `B` (Definition 4.9). -/
def acceptF {F : Type*} [Field F] [Algebra (ZMod 2) F] {κ d : ℕ}
    (B : Module.Basis (Fin κ) (ZMod 2) F) (C : MultiNondetCirc (d * κ) κ) (x : Fin d → F) :
    Set F :=
  {a | fieldBits B a ∈ C.acceptSet (vecBits B x)}

/-- `Thr(w, a) = 1` for a nondeterministic circuit `Thr` with inputs `w ∈ F^d`, `a ∈ F`. -/
def thrAccepts {F : Type*} [Field F] [Algebra (ZMod 2) F] {κ d : ℕ}
    (B : Module.Basis (Fin κ) (ZMod 2) F) (Thr : NondetCirc (d * κ + κ)) (w : Fin d → F) (a : F) :
    Prop :=
  Thr.accepts (Fin.append (vecBits B w) (fieldBits B a))

/-- The line test of Lemma 8.2: for the line `L = line u v` and a function `φ : F → F`,
`Test_L(φ) = Pr_{t ← F}[Thr(L(t), φ(t)) = 1]` if `L` is nondegenerate (`u ≠ v`), and `0` if `L` is
degenerate. For a polynomial `p`, `Test_L(p)` is `lineTest … (p.eval ·)`. -/
noncomputable def lineTest {F : Type*} [Fintype F] [Field F] [Algebra (ZMod 2) F] {κ d : ℕ}
    (B : Module.Basis (Fin κ) (ZMod 2) F) (Thr : NondetCirc (d * κ + κ)) (u v : Fin d → F)
    (φ : F → F) : ℝ :=
  open Classical in
  if u = v then 0 else probEvent (uniform F) {t | thrAccepts B Thr (line u v t) (φ t)}

/-- Binary coordinates over the prime field, for an arbitrary finite field of characteristic `p`.
Each of the `κ` basis coefficients is its canonical residue in `[0,p)`, in `p.size` bits,
least significant bit first. The length `κ * p.size` is within a factor two of `log₂ |F|`.
This representation includes odd characteristic and has polynomial-size field arithmetic. -/
noncomputable def primeFieldBits {p : ℕ} [Fact p.Prime] {F : Type*} [Field F]
    [Algebra (ZMod p) F] {κ : ℕ} (B : Module.Basis (Fin κ) (ZMod p) F) (a : F) :
    Fin (κ * p.size) → Bool :=
  fun i => (B.repr a (finProdFinEquiv.symm i).1).val.testBit
    (finProdFinEquiv.symm i).2.val

/-- Concatenate the prime-field binary coordinates of a point of `F^d`. -/
noncomputable def primeVecBits {p : ℕ} [Fact p.Prime] {F : Type*} [Field F]
    [Algebra (ZMod p) F] {κ d : ℕ} (B : Module.Basis (Fin κ) (ZMod p) F) (x : Fin d → F) :
    Fin (d * (κ * p.size)) → Bool :=
  fun i => primeFieldBits B (x (finProdFinEquiv.symm i).1) (finProdFinEquiv.symm i).2

end MultAddExt.Multiplicative


