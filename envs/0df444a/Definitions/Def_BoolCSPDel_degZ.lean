-- Prove2me | Definitions.Def_BoolCSPDel_degZ
-- name    : BoolCSPDel_degZ
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:53:53.515265+00:00
-- url     : https://prove2.me/theorems/40cee6ae-c16e-4174-989c-953dc18fc39c
-- title:
--   Integer capturing degree $\deg_{\mathbb Z}$, $d_R(b)$ and selection degree $s_R(b)$
-- statement:
--   An integer polynomial $p\in\mathbb Z[z_1,\dots,z_a]$ **captures** $R\subseteq\{0,1\}^a$ if, for every Boolean tuple $x$, $p(x)=0$ exactly when $x\in R$. The **integer capturing degree** $\deg_{\mathbb Z}(R)$ is the minimum degree of such a polynomial, and $\deg_{\mathbb Z}(\Gamma)=\max_{R\in\Gamma}\deg_{\mathbb Z}(R)$.
--
--   For an unsatisfying tuple $b$, $d_R(b)$ is the minimum degree of a polynomial that is zero on $R$ and nonzero at $b$. A polynomial $q$ **selects** $b$ if $q(b)\ne0$ and $q(x)=0$ at every other unsatisfying tuple $x$, with no condition on satisfying tuples; $s_R(b)$ is the minimum degree of such a $q$.
--
--   These degrees are the quantities the paper's bounds are stated in.
--
--   **Formalization Note** The minima are `sInf` over naturals, over all polynomials, not only multilinear ones. Every relation has a capturing polynomial, so the junk value of an empty `sInf` does not occur. The empty language has degree zero, as the paper sets.
-- source:
--   Bandekar, Sharma, Velusamy, A New Characterization of Streaming Decidability of Boolean CSPs Under Deletions, STOC 2027 submission (manuscript sha256 15f83519…), Definitions 3.5, 3.8, p.20; Definition 3.9, p.21

import Mathlib
import Definitions.Def_BoolCSPDel_Rel

namespace BoolCSPDel

/-- A Boolean tuple as an integer point of the cube. -/
def boolVal {a : ℕ} (x : Fin a → Bool) : Fin a → ℤ := fun i => if x i then 1 else 0

/-- The value `p(x)` of an integer polynomial at a Boolean tuple. -/
noncomputable def evalAt {a : ℕ} (p : MvPolynomial (Fin a) ℤ) (x : Fin a → Bool) : ℤ :=
  MvPolynomial.eval (boolVal x) p

/-- Definition 3.5, p.20: `p` captures `R` if `p(a) = 0 ⇔ a ∈ R` for every Boolean tuple `a`. -/
def Captures {k : ℕ} (R : Rel k) (p : MvPolynomial (Fin R.1) ℤ) : Prop :=
  ∀ a : Fin R.1 → Bool, evalAt p a = 0 ↔ a ∈ R.2

/-- **Integer capturing degree.** Bandekar, Sharma, Velusamy, STOC 2027 submission (manuscript
sha256 15f83519…), Definition 3.5, p.20: "The integer capturing degree `d = deg_ℤ(R)` is the minimum
degree of such a polynomial."

**Formalization Note.** `sInf` of a set of naturals. The set is nonempty for every `R` (sum of the
indicator polynomials of the unsatisfying tuples), so the junk value of `sInf ∅` never occurs. The
minimum ranges over all of `ℤ[z]`, not only multilinear polynomials. -/
noncomputable def degZ {k : ℕ} (R : Rel k) : ℕ :=
  sInf {d | ∃ p : MvPolynomial (Fin R.1) ℤ, Captures R p ∧ p.totalDegree = d}

/-- Definition 3.8, p.20: `deg_ℤ(Γ) = max_{R ∈ Γ} deg_ℤ(R)`; zero for the empty language. -/
noncomputable def degZLang {k : ℕ} (Γ : Lang k) : ℕ := Γ.sup degZ

/-- Definition 3.5, p.20: `d_R(b)`, the least degree of a polynomial that is zero on `R` and nonzero
at `b`. -/
noncomputable def dR {k : ℕ} (R : Rel k) (b : Fin R.1 → Bool) : ℕ :=
  sInf {d | ∃ p : MvPolynomial (Fin R.1) ℤ,
    (∀ a ∈ R.2, evalAt p a = 0) ∧ evalAt p b ≠ 0 ∧ p.totalDegree = d}

/-- Definition 3.9, p.21: `q` selects the unsatisfying tuple `b`: `q(b) ≠ 0` and `q(a) = 0` at every
other unsatisfying tuple. Values on satisfying tuples are unrestricted. -/
def Selects {k : ℕ} (R : Rel k) (b : Fin R.1 → Bool) (q : MvPolynomial (Fin R.1) ℤ) : Prop :=
  evalAt q b ≠ 0 ∧ ∀ a, a ∉ R.2 → a ≠ b → evalAt q a = 0

/-- Definition 3.9, p.21: `s_R(b)`, the minimum degree of a selection polynomial for `b`. -/
noncomputable def sR {k : ℕ} (R : Rel k) (b : Fin R.1 → Bool) : ℕ :=
  sInf {d | ∃ q : MvPolynomial (Fin R.1) ℤ, Selects R b q ∧ q.totalDegree = d}

/-- Every variable has exponent at most one (p.20). -/
def IsMultilinear {a : ℕ} (q : MvPolynomial (Fin a) ℤ) : Prop :=
  ∀ m ∈ q.support, ∀ i, m i ≤ 1

end BoolCSPDel


