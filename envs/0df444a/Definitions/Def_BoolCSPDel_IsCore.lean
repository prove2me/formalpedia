-- Prove2me | Definitions.Def_BoolCSPDel_IsCore
-- name    : BoolCSPDel_IsCore
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:53:42.374338+00:00
-- url     : https://prove2.me/theorems/43c02e56-bec6-471f-91cd-b2f12c44bda9
-- title:
--   Automorphisms and cores of relations and languages
-- statement:
--   An **automorphism** of $R$ is a bijection $g$ of $\{0,1\}$ such that $x\in R$ exactly when $g(x)\in R$, with $g$ applied coordinatewise. $R$ is a **core** if every map $e$ of $\{0,1\}$ with $e(R)\subseteq R$ is an automorphism. For a language $\Gamma$, an automorphism preserves membership in every relation of $\Gamma$ in both directions, and $\Gamma$ is a core if every map preserving all its relations is an automorphism.
--
--   For nonempty relations, being a core is the same as not being constant-satisfiable (Observation 3.2). Pinning (Lemma 3.4) is stated up to these automorphisms.
-- source:
--   Bandekar, Sharma, Velusamy, A New Characterization of Streaming Decidability of Boolean CSPs Under Deletions, STOC 2027 submission (manuscript sha256 15f83519…), Definition 3.1, p.18; "Cores of constraint languages", p.19

import Mathlib
import Definitions.Def_BoolCSPDel_Rel

namespace BoolCSPDel

/-- **Automorphisms and cores.** Bandekar, Sharma, Velusamy, STOC 2027 submission (manuscript sha256
15f83519…), Definition 3.1, p.18: a bijection `g` of `{0,1}` with `a ∈ R ⇔ g(a) ∈ R`, applied
coordinatewise. -/
def IsAut {k : ℕ} (R : Rel k) (g : Bool → Bool) : Prop :=
  Function.Bijective g ∧ ∀ a : Fin R.1 → Bool, a ∈ R.2 ↔ (g ∘ a) ∈ R.2

/-- Definition 3.1, p.18: every map `e` with `e(R) ⊆ R` is an automorphism. -/
def IsCore {k : ℕ} (R : Rel k) : Prop :=
  ∀ e : Bool → Bool, (∀ a ∈ R.2, (e ∘ a) ∈ R.2) → IsAut R e

/-- p.19: a bijection preserving membership in every relation of `Γ` in both directions. -/
def IsAutLang {k : ℕ} (Γ : Lang k) (g : Bool → Bool) : Prop :=
  Function.Bijective g ∧ ∀ R ∈ Γ, ∀ a : Fin R.1 → Bool, a ∈ R.2 ↔ (g ∘ a) ∈ R.2

/-- p.19: every endomorphism of `Γ` (a map preserving every relation) is an automorphism. -/
def IsCoreLang {k : ℕ} (Γ : Lang k) : Prop :=
  ∀ e : Bool → Bool, (∀ R ∈ Γ, ∀ a ∈ R.2, (e ∘ a) ∈ R.2) → IsAutLang Γ e

/-- Lemma 3.4, p.19: membership in `R` is invariant under coordinate permutations. -/
def IsSymmetric {k : ℕ} (R : Rel k) : Prop :=
  ∀ (π : Equiv.Perm (Fin R.1)) (a : Fin R.1 → Bool), a ∈ R.2 ↔ (a ∘ π) ∈ R.2

end BoolCSPDel


