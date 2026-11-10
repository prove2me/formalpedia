-- Prove2me | Definitions.Def_ObfEF_Incremental_ExtendedFrege
-- name    : ObfEF_Incremental_ExtendedFrege
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-11-10T04:56:01.777793+00:00
-- url     : https://prove2.me/theorems/9a04767c-c827-4f4e-8fce-91b62aba0715
-- title:
--   The Extended Frege system of [Li25] over {→, ⊥} and proof size (Definitions 2.5-2.6, p. 27)
-- statement:
--   The paper fixes the Extended Frege system of Li over the connectives $\{\to,\bot\}$. Its only inference rule is modus ponens (from $\varphi$ and $\varphi\to\varphi'$ derive $\varphi'$), and its axiom schemas are
--   $$\varphi\to(\varphi'\to\varphi)\ \ (K),\qquad (\varphi\to(\varphi'\to\varphi''))\to((\varphi\to\varphi')\to(\varphi\to\varphi''))\ \ (S),\qquad \neg\neg\varphi\to\varphi\ \ (D).$$
--   An **extension axiom** is a formula $z\leftrightarrow\varphi'$ ($\leftrightarrow$ the abbreviation above) where $z$ is a variable absent from $\varphi'$. An **EF proof** of $\varphi$ (Definition 2.6) is a finite sequence $\pi=(\pi_1,\dots,\pi_t)$ with $\pi_t=\varphi$ in which every $\pi_i$ is an instance of (K), (S) or (D), the conclusion of modus ponens applied to two of $\pi_1,\dots,\pi_{i-1}$, or an extension axiom $z\leftrightarrow\varphi'$ whose variable $z$ is fresh: absent from $\pi_1,\dots,\pi_{i-1}$ and from $\varphi$. The **size** of $\pi$ is
--   $$|\pi|=\sum_{i=1}^t|\pi_i|.$$
--
--   "$\mathrm{Eqv}_{C_0,C_1}$ has an EF proof of size at most $L$" is the hypothesis of the paper's rewriting theorem.
--
--   **Formalization Note.** `IsEFProof π φ` and `proofSize π`; schematic instances are arbitrary formulas.
-- source:
--   Abram, Datta, Dutta, Roy, Obfuscation via Proofs of Equivalence and Polynomial-Time Reductions to Falsifiable Assumptions, STOC 2027 submission (manuscript sha256 f9518747…), p. 27, Definitions 2.5-2.6 and the system of [Li25]

import Mathlib
import Definitions.Def_ObfEF_Incremental_Formula

/-!
# The Extended Frege system of [Li25] and the size of a proof (Definitions 2.5–2.6, p. 27)

Abram, Datta, Dutta, Roy, *Obfuscation via Proofs of Equivalence and Polynomial-Time Reductions to
Falsifiable Assumptions*, STOC 2027 submission (manuscript sha256 f9518747…), p. 27,
Definition 2.6 and the fixed system: connectives `{→, ⊥}`, modus ponens as the only inference
rule, the axiom schemas (K) `φ → (φ' → φ)`, (S) `(φ → (φ' → φ'')) → ((φ → φ') → (φ → φ''))`,
(D) `¬¬φ → φ`, and extension axioms `z ↔ φ'` with `z` absent from `φ'`, from the earlier lines and
from the proved formula. The size of a proof is `∑ |π_i|`.
-/

namespace ObfEF.Incremental

open Fml

/-- `φ` is an instance of one of the axiom schemas (K), (S), (D). -/
def IsAxiomInstance (φ : Fml) : Prop :=
  (∃ a b : Fml, φ = imp a (imp b a)) ∨
  (∃ a b c : Fml, φ = imp (imp a (imp b c)) (imp (imp a b) (imp a c))) ∨
  (∃ a : Fml, φ = imp (neg (neg a)) a)

/-- `π = (π₁, …, π_t)` is an EF proof of `φ`: `π_t = φ`, and every line is an axiom instance, the
conclusion of modus ponens from two earlier lines, or an extension axiom `z ↔ ψ` with `z` absent
from `ψ`, from all earlier lines and from `φ`. -/
def IsEFProof (π : List Fml) (φ : Fml) : Prop :=
  π.getLast? = some φ ∧
  ∀ (i : ℕ) (hi : i < π.length),
    IsAxiomInstance π[i] ∨
    (∃ (j k : ℕ) (hj : j < i) (hk : k < i),
        π[k]'(lt_trans hk hi) = imp (π[j]'(lt_trans hj hi)) π[i]) ∨
    (∃ (z : ℕ) (ψ : Fml), π[i] = iff (var z) ψ ∧ z ∉ ψ.vars ∧
        (∀ (j : ℕ) (hj : j < i), z ∉ (π[j]'(lt_trans hj hi)).vars) ∧ z ∉ φ.vars)

/-- The size `∑_i |π_i|` of a proof. -/
def proofSize (π : List Fml) : ℕ := (π.map Fml.size).sum

end ObfEF.Incremental


