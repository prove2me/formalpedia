-- Prove2me | Definitions.Def_LiftSAParity_Supplement_IsFooling
-- name    : LiftSAParity_Supplement_IsFooling
-- status  : Definition
-- author  : @iris
-- created : 2026-11-16T14:14:10.368367+00:00
-- url     : https://prove2.me/theorems/d33d8e10-5a8e-4ff3-b4bd-f8592ef093c9
-- title:
--   $(r,t,\varepsilon)$-fooling $d$-local distributions (Definition 5.3)
-- statement:
--   Let $\varphi$ be a CNF formula over $n$ blocks of $\ell$ variables, $r,t,d\in\mathbb N$ and $\varepsilon\in\mathbb R$. Write $\sigma\in\mathrm{supp}(\mathcal D)$ if $\sigma$ is a blockwise partial assignment with $|\mathrm{supp}(\sigma)|\le d$ and $\mathcal D_{\mathrm{supp}(\sigma)}(\sigma)>0$. A block $d$-local distribution $\mathcal D$ for $\varphi$ is **$(r,t,\varepsilon)$-fooling** if
--
--   1. for every $\sigma\in\mathrm{supp}(\mathcal D)$ and every set of blocks $I\supseteq\mathrm{supp}(\sigma)$ with $|I|\le t\cdot r$, the distribution $\mathcal D_I[\sigma]$ is well-defined and
--   $$
--   \Bigl|\Pr_{x\sim\widetilde{\mathcal D}_I[\sigma]}[x\in A]-2^{-k}\Bigr|\le\varepsilon
--   $$
--   for every $t$-safe affine space $A$ of codimension $k\le r$ with $\mathrm{Vars}(A)\subseteq([n]\setminus\mathrm{supp}(\sigma))\times[\ell]$;
--   2. for every affine space $A$ of codimension $r$,
--   $$
--   \Pr_{x\sim\widetilde{\mathcal D}_{\mathrm{Cl}^t(A)}}[x\in A]\le\varepsilon.
--   $$
--
--   Condition 1 says that, after conditioning on any assignment in its support, $\mathcal D$ extended uniformly looks uniform to every $t$-safe linear system of codimension at most $r$; condition 2 bounds the measure of the most constrained spaces. Theorem 5.4 turns such a distribution into a size lower bound for semantic SA(⊕).
--
--   **Formalization Note** `FoolCond1` and `FoolCond2` are the two conditions; Theorems 6.1 and 6.4 use `FoolCond1` alone. The paper's side conditions $rt\le d$ and $\varepsilon\ge0$ are hypotheses of the theorems, not part of the predicate. An affine space of codimension $r$ is nonempty (codimension is defined only for nonempty spaces, §2), and $t$-safe spaces are nonempty by definition.
-- source:
--   de Rezende, Engström, Shekhovtsov, Lifting Sherali-Adams Degree to Unary Sherali-Adams over Parities Size (manuscript, sha256 cab5a032…), §5.2, Definition 5.3, p.18, eqs. (38), (39)

import Mathlib
import Definitions.Def_LiftSAParity_IsAffineSpace
import Definitions.Def_LiftSAParity_Supplement_IsBlockLocalDist
import Definitions.Def_LiftSAParity_Supplement_extProb
import Definitions.Def_LiftSAParity_Supplement_tClosure

namespace LiftSAParity

namespace Supplement

open Classical

/-- **The first condition of being (r, t, ε)-fooling** (de Rezende–Engström–Shekhovtsov, *Lifting
Sherali-Adams Degree to Unary Sherali-Adams over Parities Size*, manuscript (sha256 cab5a032…),
Definition 5.3 (1), p.18): "For any σ ∈ supp(D) and I ⊇ supp(σ) such that |I| ≤ t·r, the
distribution D_I[σ] is well-defined and ε-fools t-safe systems of linear forms:
|Pr_{x∼D̃_I[σ]}[x ∈ A] − 2^{−k}| ≤ ε (38) for any t-safe affine space of codimension k ≤ r such
that Vars(A) ⊆ ([n] \ supp(σ)) × [ℓ]."

Here `σ ∈ supp(D)` means `|supp(σ)| ≤ d` and `D_{supp(σ)}(σ) > 0` (p.17).

**Formalization Note** `σ` is a blockwise partial assignment with support `S`. `Vars(A) ⊆ W` is
`DefinedOn A W` (a defining system using only variables of `W`). A t-safe space is nonempty
(`IsTSafe`), so `codim A` is its codimension. -/
def FoolCond1 {n ℓ : ℕ} (d r t : ℕ) (ε : ℝ)
    (D : (I : Finset (Fin n)) → BlockAssign n ℓ I → ℝ) : Prop :=
  ∀ (S : Finset (Fin n)) (σ : BlockAssign n ℓ S), S.card ≤ d → 0 < D S σ →
    ∀ I : Finset (Fin n), S ⊆ I → I.card ≤ t * r →
      CondWellDefined d D I σ ∧
      ∀ A : Set (Fin n × Fin ℓ → ZMod 2), IsAffineSpace A → IsTSafe t A → codim A ≤ r →
        DefinedOn A (Finset.univ.filter (fun v : Fin n × Fin ℓ => v.1 ∉ S)) →
        |condExtProb D I σ A - ((2 : ℝ) ^ codim A)⁻¹| ≤ ε

/-- **The second condition of being (r, t, ε)-fooling** (Definition 5.3 (2), p.18): "For any
affine space A of codimension r it holds that Pr_{x∼D̃_{Cl^t(A)}}[x ∈ A] ≤ ϵ. (39)"

**Formalization Note** "Affine space of codimension r" is a nonempty affine space (codimension is
defined for nonempty spaces only, §2, p.7). -/
def FoolCond2 {n ℓ : ℕ} (r t : ℕ) (ε : ℝ)
    (D : (I : Finset (Fin n)) → BlockAssign n ℓ I → ℝ) : Prop :=
  ∀ A : Set (Fin n × Fin ℓ → ZMod 2), IsAffineSpace A → A.Nonempty → codim A = r →
    extProb D (tClosure t A) A ≤ ε

/-- **(r, t, ε)-fooling d-local distribution** (Definition 5.3, p.18): "Given r, t, d ∈ ℕ with
rt ≤ d and ε ≥ 0 we say that a d-local distribution D is (r, t, ε)-fooling if" conditions (1) and
(2) hold. Here `D` is a block d-local distribution for the CNF `φ` over `[n] × [ℓ]`.

**Formalization Note** The side conditions `rt ≤ d` and `ε ≥ 0` are not part of the predicate;
every theorem using it assumes `rt ≤ d` (and condition (1) at `σ = ∅`, `I = ∅`, `A` the whole
cube already forces `ε ≥ 0`). -/
def IsFooling {n ℓ : ℕ} (φ : CNF (Fin n × Fin ℓ)) (d r t : ℕ) (ε : ℝ)
    (D : (I : Finset (Fin n)) → BlockAssign n ℓ I → ℝ) : Prop :=
  IsBlockLocalDist φ d D ∧ FoolCond1 d r t ε D ∧ FoolCond2 r t ε D

end Supplement

end LiftSAParity


