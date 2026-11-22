-- Prove2me | Definitions.Def_CoDecompFO_AltMatrix
-- name    : CoDecompFO_AltMatrix
-- status  : Definition
-- author  : @emmgaml
-- created : 2026-11-21T23:27:39.627248+00:00
-- url     : https://prove2.me/theorems/c507afe8-47ac-4ac9-bf64-6866ddf6cd66
-- title:
--   The matrix of the alternating prenex form of a sentence
-- statement:
--   Let $\sigma$ be a finite relational signature and let $\varphi$ be a first-order $\sigma$-sentence with equality, built from $\bot$, equalities $t_1=t_2$, atoms $R(\bar t)$, implications and universal quantifiers. This definition fixes one alternating prenex normal form
--
--   $$
--   \forall x_1\exists y_1\cdots\forall x_\ell\exists y_\ell\;\psi
--   $$
--
--   of $\varphi$, over the signature $\sigma$ with the extra binary symbol $\circ$.
--
--   1. The number of rounds $\ell$ is the number of quantifiers of $\varphi$ (`quantCount`).
--   2. The quantifiers of $\varphi$ are numbered $0,\dots,\ell-1$ in pre-order. The quantifier number $p$ owns round $p+1$: its variable becomes $x_{p+1}$ if the quantifier stands positively in $\varphi$, that is, under an even number of left-hand sides of implications, and $y_{p+1}$ if it stands negatively. The other variable of the round does not occur in $\psi$.
--   3. The matrix $\psi$ (`altMatrix`) is $\varphi$ with the quantifiers removed, each bound variable replaced by the variable of its quantifier, each equality $t_1=t_2$ replaced by $\circ(t_1,t_2)$, and each symbol of $\sigma$ kept. It is quantifier-free and has no equality atom.
--
--   The auxiliary function `matrixOf` computes the matrix of a subformula from the positions of the variables bound outside it, the number of its first quantifier, and its polarity.
--
--   On a non-empty structure $M$, the sentence $\varphi$ holds if and only if the displayed sentence holds in $M^\circ$, the structure $M$ with $\circ$ interpreted as equality. The matrix is the formula tested at the root by the bottom-up computation in the proof of Theorem 1.16.
--
--   **Formalization Note** The paper asks for an alternating prenex normal form without printing one; this one has one round per quantifier and is read off the prefix code of the sentence in one left-to-right pass. Bound variables are de Bruijn levels: $x_{p+1}$ is the variable $2p$ and $y_{p+1}$ the variable $2p+1$ of a formula with $2\ell$ bound variables.
-- source:
--   Bumpus, Gomes, Larios-Jones, Turner, Co-Decompositions and FO Model Checking, arXiv:2611.04658 (held file sha256 d550d7af…), proof of Theorem 1.16, p.41 ("Put φ into alternating prenex normal form"); ¶5.5, p.18; A.6–A.9, p.53

import Mathlib
import Definitions.Def_CoDecompFO_Sig

set_option autoImplicit false

namespace CoDecompFO

open FirstOrder

variable {σ : Sig}

/-- The number of quantifiers of a formula. In the alternating form of a sentence `φ` (Bumpus et al.,
*Co-Decompositions and FO Model Checking*, arXiv:2611.04658, held file sha256 d550d7af…, proof of
Theorem 1.16, p.41: "Put φ into alternating prenex normal form"; ¶5.5, p.18) this is the number `ℓ` of
rounds `∀x∃y`. -/
def quantCount : {n : ℕ} → σ.lang.BoundedFormula Empty n → ℕ
  | _, .falsum => 0
  | _, .equal _ _ => 0
  | _, .rel _ _ => 0
  | _, .imp f g => quantCount f + quantCount g
  | _, .all f => quantCount f + 1

/-- The symbol `∘` of `σ` with `∘` (A.7, p.53). -/
def circSym (σ : Sig) : (sigmaEq σ).lang.Relations 2 := ⟨(0 : Fin (σ.r + 1)), rfl⟩

/-- A symbol of `σ`, as a symbol of `σ` with `∘`. -/
def liftSym {a : ℕ} (R : σ.lang.Relations a) : (sigmaEq σ).lang.Relations a := ⟨R.1.succ, R.2⟩

/-- A term of a relational language is a bound variable; `renameTerm env` replaces the variable `j` by
the variable `env j`. -/
def renameTerm {n k : ℕ} (env : Fin n → Fin k) :
    σ.lang.Term (Empty ⊕ Fin n) → (sigmaEq σ).lang.Term (Empty ⊕ Fin k)
  | .var (.inl e) => e.elim
  | .var (.inr j) => .var (.inr (env j))
  | .func f _ => nomatch (show Empty from f)

/-- The matrix of the alternating form of a subformula `f` (proof of Theorem 1.16, p.41, first step;
¶5.5, p.18; A.6–A.9, p.53). The quantifiers of the sentence are numbered in pre-order, and `q` is the
number of the first quantifier of `f`. The quantifier number `p` owns round `p` of the prefix
`∀x₀∃y₀ ⋯`, whose variables sit at the positions `2p` and `2p + 1`: it binds position `2p` if it stands
positively (`neg = false`, a universal quantifier of the prefix) and `2p + 1` if it stands negatively
(`neg = true`, an existential one). `env` gives the positions of the variables bound outside `f`.
Equality atoms become `∘` atoms, and the quantifiers are removed.

**Formalization Note** The paper does not print the normal form. This one has one round per quantifier,
with one dummy variable in each round; it is the one computed by a single left-to-right scan of the
prefix code of the sentence. -/
def matrixOf (k : ℕ) : {n : ℕ} → (f : σ.lang.BoundedFormula Empty n) → (env : Fin n → Fin k) →
    (q : ℕ) → (neg : Bool) → (h : 2 * (q + quantCount f) ≤ k) →
    (sigmaEq σ).lang.BoundedFormula Empty k
  | _, .falsum, _, _, _, _ => .falsum
  | _, .equal t₁ t₂, env, _, _, _ => .rel (circSym σ) ![renameTerm env t₁, renameTerm env t₂]
  | _, .rel R ts, env, _, _, _ => .rel (liftSym R) (fun j => renameTerm env (ts j))
  | _, .imp f g, env, q, neg, h =>
      .imp (matrixOf k f env q (!neg) (by simp only [quantCount] at h; omega))
        (matrixOf k g env (q + quantCount f) neg (by simp only [quantCount] at h; omega))
  | _, .all f, env, q, neg, h =>
      matrixOf k f (Fin.snoc (α := fun _ => Fin k) env
        ⟨2 * q + neg.toNat, by have := neg.toNat_lt; simp only [quantCount] at h; omega⟩)
        (q + 1) neg (by simp only [quantCount] at h; omega)

/-- The matrix `ψ` of the alternating form `∀x₁∃y₁ ⋯ ∀x_ℓ∃y_ℓ ψ` of a sentence `φ`, with
`ℓ = quantCount φ` (proof of Theorem 1.16, p.41, first step). It is quantifier-free, has no equality
atom, and is over `σ` with `∘`. -/
def altMatrix (φ : σ.lang.Sentence) : (sigmaEq σ).lang.BoundedFormula Empty (2 * quantCount φ) :=
  matrixOf (2 * quantCount φ) φ (Fin.elim0 : Fin 0 → Fin (2 * quantCount φ)) 0 false (by omega)

end CoDecompFO


