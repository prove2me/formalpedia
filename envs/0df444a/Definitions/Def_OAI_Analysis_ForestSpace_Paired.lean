-- Prove2me | Definitions.Def_OAI_Analysis_ForestSpace_Paired
-- name    : OAI_Analysis_ForestSpace_Paired
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-15T03:51:13.351301+00:00
-- url     : https://prove2.me/theorems/b5442b44-c63e-49d7-acfc-40f0f25c7102
-- title:
--   Gate signs, corrected tails, finite lower hulls and extension by zero in forests
-- statement:
--   Let $(V,\le)$ be a partially ordered set. The first two definitions assume that $V$ is finite. They use the finite-forest notions below, for $f,k:V\to\mathbb{R}$, $s\in\mathbb{R}$ and $H\subseteq V$:
--
--   - the mass $m_k(g)=\max_{w\in V}\bigl|\sum_{g\le v\le w}k(v)\bigr|$;
--   - the selected head $h_{f,k,s}(g)$, which is the interval $\{v: a^*\le v<g\}$ for a chosen maximal $a^*<g$ with $2s\,m_k(g)\le\bigl|\sum_{a^*\le v<g}f(v)\bigr|$, or $\emptyset$ if no such $a^*$ exists;
--   - the opposite sign $\operatorname{sgn}^-(r)$, equal to $1$ for $r<0$ and $-1$ for $r\ge0$;
--   - the gate correction $c_{H,k,\sigma}(g)=\sigma(g)\,m_k(g)$ at gates $g$ of $H$ (minimal elements of $V\setminus H$), and $0$ elsewhere.
--
--   The file contains the following.
--
--   1. **Gate signs.** For finite $V$,
--   $$
--   \sigma_{f,k,s}(g)=\operatorname{sgn}^-\Bigl(\sum_{v\in h_{f,k,s}(g)}f(v)\Bigr)\in\{-1,1\}.
--   $$
--   This is the sign opposite to the $f$-sum over the selected head at $g$, and it equals $-1$ when that sum vanishes.
--   2. **Corrected tail.** For finite $V$, $H\subseteq V$ and $s,\tau\in\mathbb{R}$,
--   $$
--   \tilde k_{H,f,k,s,\tau}=c_{H,k,\sigma_{f,k,s}}+\tau\,k .
--   $$
--   That is, $\tilde k(g)=\sigma_{f,k,s}(g)\,m_k(g)+\tau k(g)$ if $g$ is a gate of $H$, and $\tilde k(g)=\tau k(g)$ otherwise.
--   3. **Finite lower hulls.** This is a lemma for arbitrary $V$. If every vertex has finitely many predecessors, meaning $\{w\in V: w\le v\}$ is finite for every $v$, then every finite set $S\subseteq V$ is contained in a finite lower set $B\subseteq V$.
--   4. **Extension by zero.** For arbitrary $V$, a finite set $B\subseteq V$ and $u:B\to\mathbb{R}$, let $\bar u:V\to\mathbb{R}$ be the finitely supported function with $\bar u(v)=u(v)$ for $v\in B$ and $\bar u(v)=0$ for $v\notin B$. The file records that $\bar u(v)=u(v)$ for $v\in B$.
--
--   Suppose a head $f$ is supported on an ancestral set $H$ and a tail $k$ is supported off $H$. With $\tau=\pm1$, the corrected tail is the vector $c\pm k$ of the paired estimate. The common correction $c=c_{H,k,\sigma_{f,k,s}}$ is supported on the gates of $H$. It is designed so that, under unit test bounds on $f$ and $k$, both $f+s(c+k)$ and $f+s(c-k)$ satisfy a disjoint-segment test bound of the form $1+12s^2$. Because $c$ is the same for both signs, it cancels when the two are averaged. The lower hull and extension by zero carry such finite-forest estimates over to forests in which every vertex has finitely many ancestors: a finitely supported vector lives on some finite lower subforest $B$.
--
--   **Formalization Note** The definitions are `gateSigns`, `correctedTail` and `finiteExtension B u`, which is built with `Finsupp.onFinset`. Its evaluation lemma is `finiteExtension_apply`. The lemma `exists_finite_lower_hull` is stated with `(Set.Iic v).Finite` and `IsLowerSet (B : Set V)`. The private lemma `dite_eq_right` is a local helper for dependent if-then-else.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/ForestSpace/Paired.lean

-- Generated from openai/math@1581d4c lean/OAI/Analysis/ForestSpace/Paired.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the ForestSpace mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_ForestSpace
import Definitions.Def_OAI_Analysis_ForestSpace_Moduli
import Definitions.Def_OAI_Analysis_ForestSpace_Segments
import Definitions.Def_OAI_Analysis_ForestSpace_FiniteGeometry

-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem dite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t : c → α} {e : ¬c → α} : (dite c t e) = e hc := @dif_neg c h hc α t e

namespace OAI

open scoped BigOperators
open Finset

namespace ForestSpace

noncomputable section
attribute [local instance] Classical.propDecidable

section FinitePaired
variable {V : Type} [Fintype V] [PartialOrder V]

noncomputable def gateSigns (f k : V → ℝ) (s : ℝ) (g : V) : ℝ :=
  oppositeSign (segSum f (selectedHead f k s g))

noncomputable def correctedTail (H : Set V) (f k : V → ℝ) (s τ : ℝ) : V → ℝ :=
  correction H k (gateSigns f k s) + τ • k

end FinitePaired

section FiniteRestriction
variable {V : Type} [PartialOrder V]

/-- The finite ancestor assumption ensures that no node inserted between two
supported coordinates is lost when we use a finite test forest. -/
 theorem exists_finite_lower_hull (hAnc : ∀ v : V, (Set.Iic v).Finite)
    (S : Finset V) : ∃ B : Finset V, S ⊆ B ∧ IsLowerSet (B : Set V) := by
  let A : Set V := ⋃ v ∈ (S : Set V), Set.Iic v
  have hA : A.Finite := S.finite_toSet.biUnion (fun v hv => hAnc v)
  refine ⟨hA.toFinset, ?_, ?_⟩
  · intro v hv
    exact hA.mem_toFinset.mpr (Set.mem_iUnion.mpr ⟨v,
      Set.mem_iUnion.mpr ⟨hv, le_rfl⟩⟩)
  · intro a b hab hb
    obtain ⟨v,hv,hbv⟩ := Set.mem_iUnion₂.mp (hA.mem_toFinset.mp hb)
    exact hA.mem_toFinset.mpr (Set.mem_iUnion₂.mpr ⟨v,hv,hab.trans hbv⟩)

/-- Extension by zero from a finite lower subforest. -/
noncomputable def finiteExtension (B : Finset V) (u : B → ℝ) : V →₀ ℝ :=
  Finsupp.onFinset B (fun v => if h : v ∈ B then u ⟨v,h⟩ else 0) (by
    intro v hv
    by_contra hn
    exact hv (dite_eq_right hn))

omit [PartialOrder V] in
@[simp] theorem finiteExtension_apply [PartialOrder V] {B : Finset V} (u : B → ℝ) (v : B) :
    finiteExtension B u v = u v := by simp [finiteExtension, v.property]

end FiniteRestriction

end

end ForestSpace

end OAI


