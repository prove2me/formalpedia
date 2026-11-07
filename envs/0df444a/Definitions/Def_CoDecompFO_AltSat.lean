-- Prove2me | Definitions.Def_CoDecompFO_AltSat
-- name    : CoDecompFO_AltSat
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T20:47:03.600944+00:00
-- url     : https://prove2.me/theorems/c7e3e7a7-41aa-49ee-ab81-bc3b4571eea6
-- title:
--   Atoms, heads of induced hypotheses, and $\forall\exists$-alternating sentences
-- statement:
--   An **atom** on $[k]$ is a symbol $R$ with a tuple of positions in $[k]$; there are $q=\sum_{R\in\sigma}k^{\mathrm{ar}(R)}$ of them. A hypothesis with a given underlying assignment is determined by the set of atoms holding in its head, the structure on $[k]$ given by the set. The hypothesis **induced** by an assignment $\beta:[k]\to G$ has the atoms $(R,a)$ with $R^G(\beta\circ a)$.
--
--   A **matrix** is a quantifier-free formula $\psi$ on $[2\ell]$ with no equality atom. For a structure $G$, the predicate here says that
--   $$
--   \forall x_1\exists y_1\cdots\forall x_\ell\exists y_\ell\;\psi(\vec x,\vec y)
--   $$
--   holds in $G$, by the game of the paper: in each round the universal player picks $x_i$ and the existential player answers $y_i$, and at the end the head induced by the chosen points must satisfy $\psi$.
--
--   **Formalization Note** An assignment is a list $l$ with $l[j]=\beta(j)$. An atom using a position outside the list does not hold. Variable $j$ of $\psi$ is read as the point $j$ of the head. On the empty structure every sentence with $\ell\geq 1$ holds, as a universal statement does.
-- source:
--   Bumpus, Gomes, Larios-Jones, Turner, Co-Decompositions and FO Model Checking, arXiv:2611.04658 (held file sha256 d550d7af…), ¶¶4.5–4.7, p.10; proof of Theorem 4.2, p.16; ¶5.5, ¶5.6, p.18

import Mathlib
import Definitions.Def_CoDecompFO_Sig

set_option autoImplicit false

namespace CoDecompFO

open FirstOrder

/-- The atomic statements on `[k]`: a symbol `R` and a tuple of positions. A hypothesis on `k` points
is determined by which of these hold in its head (Bumpus et al., arXiv:2611.04658, held file sha256
d550d7af…, proof of Theorem 4.2, p.16): "a hypothesis with underlying assignment β : [ℓ] → G_t is
determined by which of the q := ∑_{R∈σ} ℓ^{ar(R)} possible atomic relations on [ℓ] hold in its head". -/
abbrev Sig.Atom (σ : Sig) (k : ℕ) : Type := Σ i : Fin σ.r, Fin (σ.ar i) → Fin k

/-- The head of the hypothesis **induced** by the assignment `l` (¶¶4.5–4.7, p.10): the atoms on
`[k]` holding of the points selected by `l`.

**Formalization Note** The assignment `β : [k] → G` is the list `l`, with `l[j] = β(j)`. An atom with a
position outside `l` does not hold. In every use `l` has length `k` at level `0`; the partial
assignments of ¶5.9 are the shorter prefixes. -/
def atomsOf (σ : Sig) (k : ℕ) {G : Type} [σ.lang.Structure G] (l : List G) : Set (σ.Atom k) :=
  {A | ∃ args : Fin (σ.ar A.1) → G, (∀ j, l[(A.2 j).val]? = some (args j)) ∧ σ.holds A.1 args}

/-- The structure on `[k]` whose relations are given by a set of atoms: the **head** of a hypothesis
(¶4.7, p.10: "a homomorphism N → G where N = [ℓ]"). -/
@[reducible] def head {σ : Sig} {k : ℕ} (N : Set (σ.Atom k)) : σ.lang.Structure (Fin k) :=
  σ.structureOf (fun i a => (⟨i, a⟩ : σ.Atom k) ∈ N)

/-- The head with atoms `N` satisfies `ψ`, with the `j`-th bound variable of `ψ` read as the point `j`
of the head. -/
def Holds {σ : Sig} {k : ℕ} (ψ : σ.lang.BoundedFormula Empty k) (N : Set (σ.Atom k)) : Prop :=
  @FirstOrder.Language.BoundedFormula.Realize σ.lang (Fin k) (head N) Empty k ψ Empty.elim id

/-- `ψ` contains no equality atom. -/
def EqFree {σ : Sig} : {n : ℕ} → σ.lang.BoundedFormula Empty n → Prop
  | _, .falsum => True
  | _, .equal _ _ => False
  | _, .rel _ _ => True
  | _, .imp f g => EqFree f ∧ EqFree g
  | _, .all f => EqFree f

/-- `ψ` is a matrix in the paper's sense (¶5.5, p.18): quantifier-free, with no equality (the paper's
FO has no equality symbol, A.6, p.53). -/
def IsMatrix {σ : Sig} {k : ℕ} (ψ : σ.lang.BoundedFormula Empty k) : Prop :=
  ψ.IsQF ∧ EqFree ψ

/-- **The ∀∃-alternating sentence** (¶5.5, p.18; ¶5.6, p.18): `AltSat ψ m l` says that
`∀x₁∃y₁ ⋯ ∀x_m∃y_m ψ` holds in `G`, with the variables before `x₁` assigned by `l`. It is the game of
¶5.6: "In round i, the universal player chooses a value for x_i, after which the existential player
chooses a response for y_i".

**Formalization Note** On the empty structure, `AltSat ψ (m+1) l` holds, as `∀` does. -/
def AltSat {σ : Sig} {k : ℕ} {G : Type} [σ.lang.Structure G]
    (ψ : σ.lang.BoundedFormula Empty k) : ℕ → List G → Prop
  | 0, l => Holds ψ (atomsOf σ k l)
  | m + 1, l => ∀ x : G, ∃ y : G, AltSat ψ m (l ++ [x, y])

end CoDecompFO


