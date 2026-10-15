-- Prove2me | Definitions.Def_OAI_Probability_Ising_Colorings
-- name    : OAI_Probability_Ising_Colorings
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-10-14T21:55:56.819995+00:00
-- url     : https://prove2.me/theorems/3836b6ae-0b1b-47e4-b025-185dbf76d02a
-- title:
--   Colorings constant on equivalence classes and single-site flips
-- statement:
--   Let $V$ be a set and $S$ an equivalence relation on $V$, with quotient $V/S$ and class map $x\mapsto[x]$. Colorings are maps $\sigma:V\to\{-1,+1\}$. The file introduces the following.
--
--   1. **Respecting colorings.** A coloring $\sigma$ respects $S$ if it is constant on every class:
--
--      $$x\sim_S y\ \Longrightarrow\ \sigma(x)=\sigma(y)\qquad\text{for all }x,y\in V .$$
--
--   2. **The set of respecting colorings** $\mathcal C(S)=\{\sigma:V\to\{-1,+1\}\ :\ \sigma\text{ respects }S\}$, registered as a finite set whenever $V$ is finite.
--
--   3. **Component–coloring bijection.** The map sending $\sigma\in\mathcal C(S)$ to the induced coloring $[x]\mapsto\sigma(x)$ of the classes is a bijection
--
--      $$\mathcal C(S)\;\cong\;\{-1,+1\}^{V/S},$$
--
--      whose inverse composes a coloring of the classes with the class map. In particular, for finite $V$ there are exactly $2^{|V/S|}$ colorings constant on the classes of $S$.
--
--   4. **Single-site flip.** For $x\in V$, the map $\phi_x$ on $\{-1,+1\}^V$ that reverses the color at $x$ and leaves all other values unchanged. It is an involution and hence a permutation of the colorings.
--
--   In the Edwards–Sokal representation of the Ising model the classes of $S$ are the clusters of a bond configuration, and summing over the colorings that are constant on clusters produces the factor $2^{\#\text{clusters}}$ of the random-cluster weight with $q=2$; the bijection above is exactly this counting step. The single-site flip is a reindexing device for sums over configurations.
--
--   **Formalization Note** Colors are Booleans. `Respects S σ` is the class-constancy predicate and `Colorings S` the corresponding subtype, with the instance `coloringsFintype` obtained from finiteness. `componentColoringEquiv S` is an `Equiv` built with `Quotient.lift`, and `flipAt x` is the permutation of `V → Bool` obtained from an involutive function.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Ising/Colorings.lean

-- Generated from openai/math@1581d4c lean/OAI/Probability/Ising/Colorings.lean by skeleton subtraction
-- (upload_full_project.md Phase 3): Definitions bundle for the BufferedIsing mission closure.
-- Kept: reachable definitions/instances and the theorems their bodies or the node statements cite.
-- Project imports rewritten to platform modules; otherwise byte-identical to the source.
import Mathlib
import Definitions.Def_BufferedIsing
import Definitions.Def_OAI_Probability_Ising_Basic

namespace OAI

open scoped BigOperators Classical

namespace BufferedIsing

/-- A coloring is constant on precisely the components specified by a setoid. -/
def Respects {V : Type*} (S : Setoid V) (σ : V → Bool) : Prop :=
  ∀ x y, S.r x y → σ x = σ y

abbrev Colorings {V : Type*} (S : Setoid V) := {σ : V → Bool // Respects S σ}

noncomputable instance coloringsFintype {V : Type*} [Fintype V] (S : Setoid V) :
    Fintype (Colorings S) := Fintype.ofFinite _

/-- The exact bijection underlying the factor 2^(number of FK clusters). -/
def componentColoringEquiv {V : Type*} (S : Setoid V) :
    Colorings S ≃ (Quotient S → Bool) where
  toFun σ := Quotient.lift σ.val σ.property
  invFun c := ⟨fun x => c (Quotient.mk S x), fun _ _ h => congrArg c (Quotient.sound h)⟩
  left_inv σ := by apply Subtype.ext; rfl
  right_inv c := by
    funext q
    induction q using Quotient.inductionOn with | _ x => rfl

noncomputable def flipAt {V : Type*} (x : V) : (V → Bool) ≃ (V → Bool) := by
  classical
  let f := fun (σ : V → Bool) y => if y = x then !(σ y) else σ y
  have hf : Function.Involutive f := by
    intro σ
    funext y
    dsimp [f]
    by_cases h : y = x <;> simp [h]
  exact hf.toPerm f

end BufferedIsing

end OAI


