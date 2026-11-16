-- Prove2me | Definitions.Def_ConcurrentStochasticApprox_Approx_Supplement_RealTheory
-- name    : ConcurrentStochasticApprox_Approx_Supplement_RealTheory
-- status  : Definition
-- author  : @mikedeng1
-- created : 2026-11-15T17:29:18.459384+00:00
-- url     : https://prove2.me/theorems/fbb7ad0f-18da-4bd5-99ff-c2b65af7201a
-- title:
--   §4.1 — Binary real sentences, ETR, UTR and their reduction classes
-- statement:
--   For a natural number $k$, arithmetic terms use variables $x_0,\ldots,x_{k-1}$, signed binary integer constants, addition, subtraction and multiplication. Quantifier-free formulas are arbitrary Boolean combinations of $=$, $<$ and $\le$ comparisons, with truth and falsity allowed. Terms are expression trees, without expansion into dense coefficient arrays. Each constructor has a distinct self-delimiting natural-number tag and fixed arity. The sentence code is the self-delimiting code of $k$ followed by the formula code. Thus the code is injective, variable indices are in range, and its length accounts for the binary integer literals.
--
--   The two languages are
--   $$
--   \mathrm{ETR}=\{\operatorname{code}(k,\phi):\exists x\in\mathbb R^k,\ \phi(x)\},\qquad
--   \mathrm{UTR}=\{\operatorname{code}(k,\phi):\forall x\in\mathbb R^k,\ \phi(x)\}.
--   $$
--   Malformed strings belong to neither language. For $k=0$, the unique empty assignment gives the usual semantics of closed quantifier-free formulas. A binary language is in $\exists\mathbb R$ or $\mathrm{co}\text{-}\exists\mathbb R$ exactly when it is polynomial-time many-one reducible to ETR or UTR, respectively, using the published Turing-machine definition of polynomial time.
--
--   This supplies a reusable syntax and semantics for real decision reductions. The chosen prefix tags specify the binary convention left implicit by the source.
-- source:
--   Ali Asadi, Krishnendu Chatterjee, STOC 2027 submission #285 (October 2026), §4.1, printed 9 (PDF 11)

import Mathlib
import Definitions.Def_NetworkEquilibriumCLS_LinearNash_Encoding
import Definitions.Def_CookPvsNP_defs

/-! §4.1, printed p. 9 (PDF 11): the existential and universal theories of the reals.
Terms retain their expression trees; integer literals use signed binary encodings.
Constructor tags and their fixed arities make the prefix codes self-delimiting.
The variable count is encoded first; `Fin k` excludes out-of-range variable indices.
Only encodings of sentences belong to either language, so malformed strings are rejected.
-/

namespace ConcurrentStochasticApprox.Approx.Supplement

open NetworkEquilibriumCLS.LinearNash

/-- Integer polynomial expressions, without dense expansion. -/
inductive RealTerm (k : ℕ) where
  | var : Fin k → RealTerm k
  | int : ℤ → RealTerm k
  | add : RealTerm k → RealTerm k → RealTerm k
  | sub : RealTerm k → RealTerm k → RealTerm k
  | mul : RealTerm k → RealTerm k → RealTerm k

noncomputable def RealTerm.eval {k : ℕ} (x : Fin k → ℝ) : RealTerm k → ℝ
  | .var i => x i
  | .int z => (z : ℝ)
  | .add a b => a.eval x + b.eval x
  | .sub a b => a.eval x - b.eval x
  | .mul a b => a.eval x * b.eval x

def RealTerm.enc {k : ℕ} : RealTerm k → List Bool
  | .var i => encNat 0 ++ encNat i.val
  | .int z => encNat 1 ++ encInt z
  | .add a b => encNat 2 ++ a.enc ++ b.enc
  | .sub a b => encNat 3 ++ a.enc ++ b.enc
  | .mul a b => encNat 4 ++ a.enc ++ b.enc

/-- All quantifier-free Boolean combinations of real polynomial comparisons. -/
inductive RealFormula (k : ℕ) where
  | truth : RealFormula k
  | falsity : RealFormula k
  | eq : RealTerm k → RealTerm k → RealFormula k
  | lt : RealTerm k → RealTerm k → RealFormula k
  | le : RealTerm k → RealTerm k → RealFormula k
  | neg : RealFormula k → RealFormula k
  | conj : RealFormula k → RealFormula k → RealFormula k
  | disj : RealFormula k → RealFormula k → RealFormula k

def RealFormula.Holds {k : ℕ} (x : Fin k → ℝ) : RealFormula k → Prop
  | .truth => True
  | .falsity => False
  | .eq a b => a.eval x = b.eval x
  | .lt a b => a.eval x < b.eval x
  | .le a b => a.eval x ≤ b.eval x
  | .neg φ => ¬ φ.Holds x
  | .conj φ ψ => φ.Holds x ∧ ψ.Holds x
  | .disj φ ψ => φ.Holds x ∨ ψ.Holds x

def RealFormula.enc {k : ℕ} : RealFormula k → List Bool
  | .truth => encNat 0
  | .falsity => encNat 1
  | .eq a b => encNat 2 ++ a.enc ++ b.enc
  | .lt a b => encNat 3 ++ a.enc ++ b.enc
  | .le a b => encNat 4 ++ a.enc ++ b.enc
  | .neg φ => encNat 5 ++ φ.enc
  | .conj φ ψ => encNat 6 ++ φ.enc ++ ψ.enc
  | .disj φ ψ => encNat 7 ++ φ.enc ++ ψ.enc

def sentenceCode (k : ℕ) (φ : RealFormula k) : List Bool := encNat k ++ φ.enc

/-- True existential sentences, with malformed strings excluded. -/
def ETR : CookPvsNP.Lang Bool :=
  {bs | ∃ (k : ℕ) (φ : RealFormula k), sentenceCode k φ = bs ∧ ∃ x, φ.Holds x}

/-- True universal sentences, with malformed strings excluded. -/
def UTR : CookPvsNP.Lang Bool :=
  {bs | ∃ (k : ℕ) (φ : RealFormula k), sentenceCode k φ = bs ∧ ∀ x, φ.Holds x}

def InExistsR (L : CookPvsNP.Lang Bool) : Prop := CookPvsNP.PolyReducible L ETR

def InCoExistsR (L : CookPvsNP.Lang Bool) : Prop := CookPvsNP.PolyReducible L UTR

end ConcurrentStochasticApprox.Approx.Supplement


