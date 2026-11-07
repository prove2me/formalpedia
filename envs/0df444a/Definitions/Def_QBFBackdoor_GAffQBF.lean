-- Prove2me | Definitions.Def_QBFBackdoor_GAffQBF
-- name    : QBFBackdoor_GAffQBF
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T11:32:17.284291+00:00
-- url     : https://prove2.me/theorems/ac49769e-7a0c-4549-8681-20a3098a8c1b
-- title:
--   QBF with guarded affine atoms $\bigl(\bigoplus_{v\in A}x_v=b\bigr)\vee T$
-- statement:
--   An **affine atom** is an equation $\bigl(\bigoplus_{v\in A}x_v\bigr)=b$ over $\mathbb F_2$, represented by the pair $(A,b)$ of a variable set and a right-hand side $b\in\{0,1\}$. A **guarded affine atom** $(A,b)\vee T$ adds a clausal guard $T$, a set of literals: it is satisfied by $x$ when some literal of $T$ is true under $x$ or
--
--   $$
--   \sum_{v\in A}x_v\equiv b \pmod 2 .
--   $$
--
--   An unguarded affine atom is the case $T=\emptyset$. Assigning all guard variables turns a guarded atom into $\top$ or into the original equation.
--
--   A **guarded-affine QBF** is a prefix $Q$ on $x_1,\dots,x_n$ together with a conjunction of $m$ guarded affine atoms; its truth is that of $Q.F$ for this conjunctive matrix.
--
--   This is the representation in which the paper states hardness for the affine target class: the reverse reduction of Lemma 4.4 attaches clausal guards to equality atoms, and after the selector variables are assigned the residual atoms are affine equations.
--
--   **Formalization Note** The guard is a `Finset (Fin n × Bool)`, with `(v, true)` the literal $x_v$. Instances bundle $n$ and $m$ (`GAffInst`, and `GAffInstB` with a supplied variable set).
-- source:
--   Eriksson, Lagerkvist, Ordyniak, Osipov, Panolan, Rychlicki, Backdoors for Quantified Boolean Formulas, arXiv:2604.15927 (held version, sha256 3ea1662e…), §3.1, pp.14–15 (affine atoms, guarded atoms); Lemma 4.4, pp.20–21

import Mathlib
import Definitions.Def_QBFBackdoor_PrefixHolds

namespace QBFBackdoor

/-- **A guarded affine atom** `((⊕_{v ∈ E} x_v) = b) ∨ T`. Eriksson, Lagerkvist, Ordyniak, Osipov,
Panolan, Rychlicki, *Backdoors for Quantified Boolean Formulas*, arXiv:2604.15927 (held version,
sha256 3ea1662e…), §3.1, pp.14–15: affine atoms are "(ℓ1 ⊕ ℓ2 ⊕ · · · ⊕ ℓk) = b … represent[ed] by
a pair (A, b), where A is a set of variables and b ∈ {0, 1}", and "When explicitly stated, we also
allow a guarded atom R(x)∨T(z), stored as the original atom and a clausal guard. Assigning all
guard variables simplifies it to ⊤ or to the original atom." Lemma 4.4, pp.20–21: "For the affine
target, keeping the guarded equality atoms gives affine equations after restriction."

`eqv` is the variable set `A`, `rhs` the right-hand side `b`, and `guard` the clausal guard `T`,
a set of literals (`(v, true)` = `x_v`, `(v, false)` = `¬x_v`). An unguarded affine equation is
the case `guard = ∅`. -/
structure GAff (n : ℕ) where
  eqv : Finset (Fin n)
  rhs : Bool
  guard : Finset (Fin n × Bool)

/-- An assignment `x` satisfies the guarded atom: some guard literal is true, or the equation
`Σ_{v ∈ A} x_v ≡ b (mod 2)` holds. -/
def GAff.Sat {n : ℕ} (C : GAff n) (x : Fin n → Bool) : Prop :=
  (∃ l ∈ C.guard, x l.1 = l.2) ∨ (C.eqv.filter (fun v => x v = true)).card % 2 = C.rhs.toNat

/-- **A guarded-affine QBF**: a prefix `q` over `Fin n` (`true` = ∃, variables quantified in index
order) and a conjunction of `m` guarded affine atoms. -/
structure GAffQBF (n m : ℕ) where
  q : Fin n → Bool
  atom : Fin m → GAff n

/-- The conjunctive matrix is true under `x`. -/
def GAffQBF.Sat {n m : ℕ} (ψ : GAffQBF n m) (x : Fin n → Bool) : Prop :=
  ∀ i, (ψ.atom i).Sat x

/-- Truth of the guarded-affine QBF (§3.2, p.15). -/
def GAffQBF.holds {n m : ℕ} (ψ : GAffQBF n m) : Prop :=
  PrefixHolds ψ.q ψ.Sat

end QBFBackdoor


