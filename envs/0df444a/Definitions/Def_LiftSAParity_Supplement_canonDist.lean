-- Prove2me | Definitions.Def_LiftSAParity_Supplement_canonDist
-- name    : LiftSAParity_Supplement_canonDist
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:14:44.370009+00:00
-- url     : https://prove2.me/theorems/4ef3106a-76ba-4807-830b-7ffebf36fc69
-- title:
--   The canonical distributions $\mathcal D^\varphi$ and the parameters $m$, $p$ of Theorem 6.1
-- statement:
--   Let $\varphi$ be a CNF formula over $n$ blocks of $\ell$ variables.
--
--   1. For a set of blocks $I\subseteq[n]$, the **canonical distribution** $\mathcal D^\varphi_I$ is the uniform distribution on
--   $$
--   \{x\in\{0,1\}^{I\times[\ell]} : x \text{ falsifies no clause of } \varphi \text{ whose variables all lie in } I\times[\ell]\}.
--   $$
--   2. $m$ is the maximum, over sets $I$ of at most $d$ blocks, of the number of clauses of $\varphi$ whose variables all lie in $I\times[\ell]$.
--   3. The **uniform-extension falsification bound** with parameter $p$ holds if, for every blockwise partial assignment $\sigma$ that falsifies no clause and every set $I\supseteq\mathrm{supp}(\sigma)$ of at most $d$ blocks, a uniformly random extension of $\sigma$ to $I\times[\ell]$ falsifies some clause of $\varphi$ whose variables all lie in $I\times[\ell]$ with probability at most $p$.
--
--   These are the data of Theorem 6.1, which gives a sufficient condition for $\mathcal D^\varphi$ to be fooling.
--
--   **Formalization Note** `canonDist φ I` is defined for every $I$. When no assignment avoids the axioms its values are all $0$, so the hypothesis that $\mathcal D^\varphi$ is a block $d$-local distribution then fails; this is the paper's remark that at least one such $x$ must exist for $\mathcal D^\varphi_I$ to be well-defined. `maxLocalClauses φ d` is $m$ and `UniformExtFalsifyBound φ d p` is item 3.
-- source:
--   de Rezende, Engström, Shekhovtsov, Lifting Sherali-Adams Degree to Unary Sherali-Adams over Parities Size (manuscript, sha256 cab5a032…), §6.1, p.20 (canonical distributions; Theorem 6.1)

import Mathlib
import Definitions.Def_LiftSAParity_Supplement_IsBlockLocalDist

namespace LiftSAParity

namespace Supplement

open Classical

/-- The blockwise partial assignment `τ` falsifies no clause of `φ` whose variables all lie in its
blocks ("x does not violate axioms of φ", de Rezende–Engström–Shekhovtsov, *Lifting Sherali-Adams
Degree to Unary Sherali-Adams over Parities Size*, manuscript (sha256 cab5a032…), §6.1, p.20). -/
def NoFalsified {n ℓ : ℕ} (φ : CNF (Fin n × Fin ℓ)) {I : Finset (Fin n)}
    (τ : BlockAssign n ℓ I) : Prop :=
  ∀ C ∈ φ, ¬ FalsifiesOn τ C

/-- **The canonical distributions** `D^φ` (§6.1, p.20): "For I ⊆ [n] of size at most d, let us set
D^φ_I to be the uniform distribution on the set {x ∈ {0,1}^{I×[ℓ]} : x does not violate axioms of
φ}."

**Formalization Note** Defined for every `I` (the constraint `|I| ≤ d` enters through
`IsBlockLocalDist φ d (canonDist φ)`). If no `x` satisfies the axioms the values are all `0`, so
`D^φ_I` is not a probability distribution and the hypothesis "D^φ is a d-local distribution"
fails, which is the paper's "there should be at least one x … for D^φ_I to be well-defined". -/
noncomputable def canonDist {n ℓ : ℕ} (φ : CNF (Fin n × Fin ℓ)) (I : Finset (Fin n))
    (τ : BlockAssign n ℓ I) : ℝ :=
  if NoFalsified φ τ then
    1 / ((Finset.univ.filter (fun τ' : BlockAssign n ℓ I => NoFalsified φ τ')).card : ℝ)
  else 0

/-- `m` of Theorem 6.1 (p.20): "the maximum number of clauses of φ whose variables all lie in some
set of at most d blocks", i.e. `max_{I ⊆ [n], |I| ≤ d} |{C ∈ φ : vars(C) ⊆ I × [ℓ]}|`. -/
noncomputable def maxLocalClauses {n ℓ : ℕ} (φ : CNF (Fin n × Fin ℓ)) (d : ℕ) : ℕ :=
  (Finset.univ.filter (fun I : Finset (Fin n) => I.card ≤ d)).sup
    (fun I => (φ.filter (fun C => ∀ l ∈ C, l.1.1 ∈ I)).card)

/-- The hypothesis of Theorem 6.1 (p.20): "every blockwise partial assignment that does not
falsify any clause, when extended uniformly to any set of at most d blocks, falsifies a clause
with probability at most p". For every blockwise `σ` (support `S`) falsifying no clause inside
its blocks and every `I ⊇ S` with `|I| ≤ d`, a uniformly random `τ ∈ {0,1}^{I×[ℓ]}` agreeing with
`σ` falsifies some clause of `φ` whose variables all lie in `I × [ℓ]` with probability `≤ p`. -/
def UniformExtFalsifyBound {n ℓ : ℕ} (φ : CNF (Fin n × Fin ℓ)) (d : ℕ) (p : ℝ) : Prop :=
  ∀ (S : Finset (Fin n)) (σ : BlockAssign n ℓ S), NoFalsified φ σ →
    ∀ I : Finset (Fin n), S ⊆ I → I.card ≤ d →
      ((Finset.univ.filter
          (fun τ : BlockAssign n ℓ I => Compat τ σ ∧ ∃ C ∈ φ, FalsifiesOn τ C)).card : ℝ) /
        ((Finset.univ.filter (fun τ : BlockAssign n ℓ I => Compat τ σ)).card : ℝ) ≤ p

end Supplement

end LiftSAParity


