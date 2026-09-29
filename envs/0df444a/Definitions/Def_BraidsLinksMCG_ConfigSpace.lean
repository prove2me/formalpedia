-- Prove2me | Definitions.Def_BraidsLinksMCG_ConfigSpace
-- name    : BraidsLinksMCG_ConfigSpace
-- status  : Definition
-- author  : @Lucas
-- created : 2026-09-13T18:57:12.770988+00:00
-- url     : https://prove2.me/theorems/a3deed61-1ca1-4d3a-b07a-11fd40c40bad
-- title:
--   Configuration spaces $F_{0,n}E^2$, $B_{0,n}E^2$ and the braid groups of the plane
-- statement:
--   The configuration spaces of the plane $E^2 = \mathbb{C}$ and the fundamental groups attached to
--   them.
--
--   The **ordered configuration space** $F_{0,n}E^2$ is the space of injective $n$-tuples of complex
--   numbers, topologized as a subspace of $\mathbb{C}^n$. Two ordered configurations are identified
--   when they differ by a permutation of the labels; the quotient, with the quotient topology, is
--   the **unordered configuration space** $B_{0,n}E^2$, and $p : F_{0,n}E^2 \to B_{0,n}E^2$ is the
--   natural projection.
--
--   The base configuration is $(1, 2, \dots, n)$, the analogue of the book's
--   $((1,0), \dots, (n,0))$, and its image is the base point of $B_{0,n}E^2$. The **pure braid
--   group** is $P_n = \pi_1 F_{0,n}E^2$ and the **braid group of the plane** is $\pi_1 B_{0,n}E^2$,
--   both at those base points.
--
--   The file also provides the two maps used in the Fadell–Neuwirth argument: the projection
--   $F_{0,n+1}E^2 \to F_{0,n}E^2$ that forgets the last point (equation (1-4)) and the inclusion of
--   the plane punctured at the first $n$ base points as the last coordinate (equation (1-6)),
--   together with the elementary facts that both maps are continuous and send base point to base
--   point.
-- source:
--   Joan S. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82, Princeton University Press, 1974, Chapter 1, §1.1–§1.4, pp. 5–18 (configuration spaces p. 11, maps (1-4) p. 12 and (1-6) p. 14)

import Mathlib

/-!
# Configuration spaces of the plane and the geometric braid groups

Following Birman, *Braids, Links, and Mapping Class Groups*, Chapter 1 (§1.1–§1.4), we set up,
for the plane `E² = ℂ`:

* the ordered configuration space `F_{0,n}E²` of `n` distinct labelled points;
* the unordered configuration space `B_{0,n}E²`, its quotient by the symmetric group;
* the pure braid group `P_n = π₁ F_{0,n}E²` and the braid group `π₁ B_{0,n}E²`;
* the projection `F_{0,n+1}E² → F_{0,n}E²` forgetting the last point (equation (1-4)) and the
  inclusion of the punctured plane as the last coordinate (equation (1-6)).

The base configuration is `(1, 2, …, n) ∈ ℂⁿ`, the analogue of the book's `((1,0), …, (n,0))`.
-/

namespace BraidsLinksMCG

noncomputable section

/-- The ordered configuration space `F_{0,n}E²`: injective `n`-tuples of points of the plane. -/
abbrev OrderedConfig (n : ℕ) : Type := {p : Fin n → ℂ // Function.Injective p}

/-- Two ordered configurations are identified when they differ by a permutation of the labels. -/
def configSetoid (n : ℕ) : Setoid (OrderedConfig n) where
  r p q := ∃ g : Equiv.Perm (Fin n), q.1 = p.1 ∘ g
  iseqv :=
    { refl := fun _ => ⟨1, rfl⟩
      symm := fun {p q} h => by
        obtain ⟨g, hg⟩ := h
        refine ⟨g.symm, ?_⟩
        funext i
        simp [hg]
      trans := fun {p q r} h h' => by
        obtain ⟨g, hg⟩ := h
        obtain ⟨g', hg'⟩ := h'
        exact ⟨g * g', by funext i; simp [hg', hg, Function.comp_def]⟩ }

/-- The unordered configuration space `B_{0,n}E²`: ordered configurations modulo relabelling,
with the quotient topology. -/
abbrev UnorderedConfig (n : ℕ) : Type := Quotient (configSetoid n)

/-- The natural projection `p : F_{0,n}E² → B_{0,n}E²`. -/
def configProj (n : ℕ) : C(OrderedConfig n, UnorderedConfig n) :=
  ⟨fun p => Quotient.mk (configSetoid n) p, continuous_quotient_mk'⟩

/-- The base configuration `(1, 2, …, n)` of `F_{0,n}E²`. -/
def baseOrdered (n : ℕ) : OrderedConfig n :=
  ⟨fun i => ((i : ℕ) + 1 : ℂ), by
    intro i j hij
    have h1 : ((i : ℕ) : ℂ) = ((j : ℕ) : ℂ) := add_right_cancel hij
    exact Fin.ext (by exact_mod_cast h1)⟩

/-- The base point of `B_{0,n}E²`, the image of `baseOrdered n`. -/
def baseUnordered (n : ℕ) : UnorderedConfig n := configProj n (baseOrdered n)

/-- The pure braid group `P_n = π₁(F_{0,n}E²)`. -/
abbrev PureBraidGroup (n : ℕ) : Type := FundamentalGroup (OrderedConfig n) (baseOrdered n)

/-- The braid group of the plane `π₁(B_{0,n}E²)`. -/
abbrev GeomBraidGroup (n : ℕ) : Type := FundamentalGroup (UnorderedConfig n) (baseUnordered n)

/-- The projection `F_{0,n+1}E² → F_{0,n}E²` of equation (1-4) forgetting the last point. -/
def configForget (n : ℕ) : C(OrderedConfig (n + 1), OrderedConfig n) where
  toFun p := ⟨fun i => p.1 i.castSucc, fun i j hij =>
    Fin.castSucc_injective n (p.2 hij)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_pi fun i => (continuous_apply _).comp continuous_subtype_val

@[simp] lemma configForget_base (n : ℕ) :
    configForget n (baseOrdered (n + 1)) = baseOrdered n := by
  apply Subtype.ext
  funext i
  rfl

/-- The plane punctured at the `n` base points `1, 2, …, n`, i.e. `E² - Q_n`. -/
abbrev PuncturedPlane (n : ℕ) : Type := {z : ℂ // ∀ j : Fin n, z ≠ ((j : ℕ) + 1 : ℂ)}

/-- The base point `n + 1` of the punctured plane `E² - Q_n`. -/
def basePunctured (n : ℕ) : PuncturedPlane n :=
  ⟨((n : ℕ) + 1 : ℂ), by
    intro j hj
    have h1 : ((n : ℕ) : ℂ) = ((j : ℕ) : ℂ) := add_right_cancel hj
    have h2 : n = (j : ℕ) := by exact_mod_cast h1
    have h3 := j.isLt
    omega⟩

/-- The inclusion `E² - Q_n → F_{0,n+1}E²` of equation (1-6), sending `z` to the configuration
`(1, 2, …, n, z)`. -/
def configIncl (n : ℕ) : C(PuncturedPlane n, OrderedConfig (n + 1)) where
  toFun z := ⟨Fin.snoc (fun k : Fin n => ((k : ℕ) + 1 : ℂ)) z.1, by
    intro i j hij
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => rfl
      | cast b =>
        rw [Fin.snoc_last, Fin.snoc_castSucc] at hij
        exact absurd hij (z.2 b)
    | cast a =>
      induction j using Fin.lastCases with
      | last =>
        rw [Fin.snoc_last, Fin.snoc_castSucc] at hij
        exact absurd hij.symm (z.2 a)
      | cast b =>
        rw [Fin.snoc_castSucc, Fin.snoc_castSucc] at hij
        have h1 : ((a : ℕ) : ℂ) = ((b : ℕ) : ℂ) := add_right_cancel hij
        exact congrArg Fin.castSucc (Fin.ext (by exact_mod_cast h1))⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    refine continuous_pi fun i => ?_
    induction i using Fin.lastCases with
    | last => simpa only [Fin.snoc_last] using continuous_subtype_val
    | cast a => simpa only [Fin.snoc_castSucc] using continuous_const

@[simp] lemma configIncl_base (n : ℕ) :
    configIncl n (basePunctured n) = baseOrdered (n + 1) := by
  apply Subtype.ext
  funext i
  show Fin.snoc (α := fun _ => ℂ) (fun k : Fin n => ((k : ℕ) + 1 : ℂ))
      (((n : ℕ) + 1 : ℂ)) i = ((i : ℕ) + 1 : ℂ)
  induction i using Fin.lastCases with
  | last => simp
  | cast a => simp

/-- The fundamental group of the punctured plane `E² - Q_n` at the base point `n + 1`. -/
abbrev PuncturedPlaneGroup (n : ℕ) : Type :=
  FundamentalGroup (PuncturedPlane n) (basePunctured n)

end

end BraidsLinksMCG


