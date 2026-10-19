-- Prove2me | Definitions.Def_QAlgorithms_Defs_TannerDecoder
-- name    : QAlgorithms_Defs_TannerDecoder
-- status  : Definition
-- author  : @Goku
-- created : 2026-10-18T18:58:37.521225+00:00
-- url     : https://prove2.me/theorems/9116d1eb-3904-4cc5-9f23-39872763d1ac
-- title:
--   The quadripartite left-right Cayley complex, the codes `C₀`, `C₁`, and the sequential decoder
-- statement:
--   # The quadripartite left-right Cayley complex, the codes `C₀`, `C₁`, and the sequential decoder
--   (shared definition layer)
--
--   A. Leverrier, G. Zémor, *Efficient decoding up to a constant fraction of the code length for
--   asymptotically good quantum codes* (arXiv:2208.05537v3), cited "LZ-dec p.N" (PDF pages), §§2.5,
--   4, 5.
--
--   Conventions. `G` is a finite group, `A, B ⊆ G`. A vertex `(g, (i, j)) : G × (Bool × Bool)` is the
--   source's `(g, ij) ∈ V_{ij}` (`i` the first bit, `j` the second); `V₀ = V₀₀ ∪ V₁₁` (`i = j`),
--   `V₁ = V₀₁ ∪ V₁₀` (`i ≠ j`). The squares are indexed by `G × A × B`: `(g, a, b)` is
--   `{(g,00), (ag,01), (gb,10), (agb,11)}` (p.10), an injective indexing, so `F₂^Q` is
--   `G × A × B → ZMod 2` and `n = |G| Δ²`.
--   -/
--
--   namespace QAlgorithms
--
--   variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]
--
--   /-- LZ-dec p.10, §2.5: the index of the square `φ_v(a, b)` of the four explicit formulas of p.10:
--   `v = (g, 00)`: `(g, a, b)`; `v = (g, 01)`: `(a⁻¹g, a, b)`; `v = (g, 10)`: `(gb⁻¹, a, b)`;
--   `v = (g, 11)`: `(a⁻¹gb⁻¹, a, b)`.
-- source:
--   Source references and exact conventions are recorded in each declaration docstring. algorithms\QAlgorithms\Defs\TannerDecoder.lean

import Definitions.Def_QAlgorithms_Defs_LeftRightComplex
/-!
# The quadripartite left-right Cayley complex, the codes `C₀`, `C₁`, and the sequential decoder
(shared definition layer)

A. Leverrier, G. Zémor, *Efficient decoding up to a constant fraction of the code length for
asymptotically good quantum codes* (arXiv:2208.05537v3), cited "LZ-dec p.N" (PDF pages), §§2.5,
4, 5.

Conventions. `G` is a finite group, `A, B ⊆ G`. A vertex `(g, (i, j)) : G × (Bool × Bool)` is the
source's `(g, ij) ∈ V_{ij}` (`i` the first bit, `j` the second); `V₀ = V₀₀ ∪ V₁₁` (`i = j`),
`V₁ = V₀₁ ∪ V₁₀` (`i ≠ j`). The squares are indexed by `G × A × B`: `(g, a, b)` is
`{(g,00), (ag,01), (gb,10), (agb,11)}` (p.10), an injective indexing, so `F₂^Q` is
`G × A × B → ZMod 2` and `n = |G| Δ²`.
-/

namespace QAlgorithms

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

/-- LZ-dec p.10, §2.5: the index of the square `φ_v(a, b)` of the four explicit formulas of p.10:
`v = (g, 00)`: `(g, a, b)`; `v = (g, 01)`: `(a⁻¹g, a, b)`; `v = (g, 10)`: `(gb⁻¹, a, b)`;
`v = (g, 11)`: `(a⁻¹gb⁻¹, a, b)`. -/
def qtPhi (A B : Finset G) (v : G × (Bool × Bool)) (a : A) (b : B) : G × A × B :=
  ((if v.2.2 then (a : G)⁻¹ else 1) * v.1 * (if v.2.1 then (b : G)⁻¹ else 1), a, b)

/-- LZ-dec pp.10, 18: the local view `x_v` of `x ∈ F₂^Q` on `Q(v)`, read through `φ_v`. -/
def qtLocalView {A B : Finset G} (x : G × A × B → ZMod 2) (v : G × (Bool × Bool)) :
    A × B → ZMod 2 :=
  fun ab => x (qtPhi A B v ab.1 ab.2)

/-- LZ-dec pp.10, 18: the vector of `F₂^Q` supported on `Q(v)` that equals `c` through `φ_v`
(`q ∈ Q(v)` iff `q = φ_v(q_a, q_b)`). -/
def qtPush {A B : Finset G} (v : G × (Bool × Bool)) (c : A × B → ZMod 2) : G × A × B → ZMod 2 :=
  fun q => if q.1 = (qtPhi A B v q.2.1 q.2.2).1 then c (q.2.1, q.2.2) else 0

/-- LZ-dec p.11: `C₀ = Tan(G₀^□, (C_A ⊗ C_B)^⊥) = Tan(G₀^□, C_A^⊥ ⊗ F₂^B + F₂^A ⊗ C_B^⊥)`: every
local view at a vertex of `V₀ = V₀₀ ∪ V₁₁` is a dual tensor codeword of the dual codes. -/
def qtCode0 {A B : Finset G} (CA : Submodule (ZMod 2) (A → ZMod 2))
    (CB : Submodule (ZMod 2) (B → ZMod 2)) : Submodule (ZMod 2) (G × A × B → ZMod 2) where
  carrier := {x | ∀ v : G × (Bool × Bool), v.2.1 = v.2.2 →
    qtLocalView x v ∈ dualTensorCode (codeDual CA) (codeDual CB)}
  add_mem' := by
    intro x y hx hy v hv
    exact add_mem (hx v hv) (hy v hv)
  zero_mem' := by
    intro v _
    exact zero_mem _
  smul_mem' := by
    intro c x hx v hv
    exact Submodule.smul_mem _ c (hx v hv)

/-- LZ-dec p.11: `C₁ = Tan(G₁^□, (C_A^⊥ ⊗ C_B^⊥)^⊥)`: every local view at a vertex of
`V₁ = V₀₁ ∪ V₁₀` is a codeword of `C_A ⊗ F₂^B + F₂^A ⊗ C_B`. -/
def qtCode1 {A B : Finset G} (CA : Submodule (ZMod 2) (A → ZMod 2))
    (CB : Submodule (ZMod 2) (B → ZMod 2)) : Submodule (ZMod 2) (G × A × B → ZMod 2) where
  carrier := {x | ∀ v : G × (Bool × Bool), v.2.1 ≠ v.2.2 → qtLocalView x v ∈ dualTensorCode CA CB}
  add_mem' := by
    intro x y hx hy v hv
    exact add_mem (hx v hv) (hy v hv)
  zero_mem' := by
    intro v _
    exact zero_mem _
  smul_mem' := by
    intro c x hx v hv
    exact Submodule.smul_mem _ c (hx v hv)

/-- LZ-dec pp.4, 9, 10: the span of the `σ_x`-type generators, codewords of `C_A ⊗ C_B` placed on
the `Q`-neighbourhoods of the vertices of `V₀` (the `X`-part `C₀^⊥` of the stabilizer group); a
correction `ê` of a `σ_x`-error `e` is valid iff `e + ê` lies in this span. -/
def qtSigmaXSpan {A B : Finset G} (CA : Submodule (ZMod 2) (A → ZMod 2))
    (CB : Submodule (ZMod 2) (B → ZMod 2)) : Submodule (ZMod 2) (G × A × B → ZMod 2) :=
  Submodule.span (ZMod 2) {y | ∃ (v : G × (Bool × Bool)) (c : A × B → ZMod 2),
    v.2.1 = v.2.2 ∧ c ∈ tensorCode CA CB ∧ y = qtPush v c}

/-- LZ-dec p.5, p.18 (Algorithm 1, preprocessing, `v ∈ V₁`): `ε_v` is a minimum-weight local
error with the same local syndrome as `e_v`, i.e. `e_v + ε_v ∈ C_A ⊗ F₂^B + F₂^A ⊗ C_B` and no
`ε'` with that property is lighter (any minimizer is allowed). -/
def IsMinLocalCorrection {A B : Finset G} (CA : Submodule (ZMod 2) (A → ZMod 2))
    (CB : Submodule (ZMod 2) (B → ZMod 2)) (e : G × A × B → ZMod 2) (v : G × (Bool × Bool))
    (εv : A × B → ZMod 2) : Prop :=
  qtLocalView e v + εv ∈ dualTensorCode CA CB ∧
    ∀ ε' : A × B → ZMod 2, qtLocalView e v + ε' ∈ dualTensorCode CA CB →
      hammingNorm εv ≤ hammingNorm ε'

/-- LZ-dec pp.5, 18: the mismatch `Z = Σ_{v ∈ V₁} ε_v` (each `ε_v` placed on `Q(v)`). -/
def qtMismatch {A B : Finset G} (εsel : G × (Bool × Bool) → A × B → ZMod 2) :
    G × A × B → ZMod 2 :=
  ∑ v ∈ Finset.univ.filter (fun v : G × (Bool × Bool) => v.2.1 ≠ v.2.2), qtPush v (εsel v)

/-- LZ-dec p.19, Algorithm 2: the state `(Ĉ₀, Ĉ₁, R̂₀, R̂₁, Ẑ)` of the sequential mismatch
decomposition (`C b` is `Ĉ_b`, `R b` is `R̂_b`). -/
structure SeqDecState (Q : Type*) where
  /-- `Ĉ₀`, `Ĉ₁`. -/
  C : Bool → Q → ZMod 2
  /-- `R̂₀`, `R̂₁`. -/
  R : Bool → Q → ZMod 2
  /-- The current mismatch `Ẑ`. -/
  Z : Q → ZMod 2

/-- LZ-dec p.19, Algorithm 2 line 1: `Ĉ₀ = R̂₀ = Ĉ₁ = R̂₁ = 0`, `Ẑ = Z`. -/
def seqDecInit {Q : Type*} (Z : Q → ZMod 2) : SeqDecState Q :=
  ⟨0, 0, Z⟩

/-- LZ-dec pp.17, 19, Algorithm 2 lines 2–7 (one iteration, `σ_x`-type errors): while `Ẑ ≠ 0`,
choose `v ∈ V_{ij}` and a non-zero dual tensor codeword `x_v = c_v + r_v` on `Q(v)`
(`c_v ∈ C_A ⊗ F₂^B`, `r_v ∈ F₂^A ⊗ C_B`) with `|Ẑ| − |Ẑ + x_v| ⩾ (1 − ε)|x_v|`, the decomposition
minimising `‖c_v‖ + ‖r_v‖`, and update `Ĉ_j += c_v`, `R̂_i += r_v`, `Ẑ += x_v`.
Nondeterministic (any admissible `v`, `x_v`, minimal decomposition); "Failure" is a state with
`Ẑ ≠ 0` admitting no step. -/
def SeqDecStep {A B : Finset G} (CA : Submodule (ZMod 2) (A → ZMod 2))
    (CB : Submodule (ZMod 2) (B → ZMod 2)) (ε : ℝ) (s s' : SeqDecState (G × A × B)) : Prop :=
  s.Z ≠ 0 ∧ ∃ (v : G × (Bool × Bool)) (c r : A × B → ZMod 2),
    c ∈ columnCode CA B ∧ r ∈ rowCode A CB ∧ c + r ≠ 0 ∧
    (1 - ε) * (hammingNorm (qtPush v (c + r)) : ℝ) ≤
      (hammingNorm s.Z : ℝ) - (hammingNorm (s.Z + qtPush v (c + r)) : ℝ) ∧
    (∀ c' ∈ columnCode CA B, ∀ r' ∈ rowCode A CB, c' + r' = c + r →
      nonzeroCols c + nonzeroRows r ≤ nonzeroCols c' + nonzeroRows r') ∧
    s' = ⟨Function.update s.C v.2.2 (s.C v.2.2 + qtPush v c),
      Function.update s.R v.2.1 (s.R v.2.1 + qtPush v r), s.Z + qtPush v (c + r)⟩

/-- LZ-dec pp.19, 24: a run of `m` iterations of Algorithm 2 from `seqDecInit Z`. -/
def IsSeqDecRun {A B : Finset G} (CA : Submodule (ZMod 2) (A → ZMod 2))
    (CB : Submodule (ZMod 2) (B → ZMod 2)) (ε : ℝ) (Z : G × A × B → ZMod 2)
    (s : ℕ → SeqDecState (G × A × B)) (m : ℕ) : Prop :=
  s 0 = seqDecInit Z ∧ ∀ i < m, SeqDecStep CA CB ε (s i) (s (i + 1))

/-- LZ-dec pp.17–18, Algorithm 1 lines 10–11, 14: the postprocessing for a `σ_x`-error,
`ê = Σ_{v ∈ V₁₀} ε_v + Ĉ₀ + R̂₁`. -/
def seqDecOutput {A B : Finset G} (εsel : G × (Bool × Bool) → A × B → ZMod 2)
    (s : SeqDecState (G × A × B)) : G × A × B → ZMod 2 :=
  (∑ v ∈ Finset.univ.filter (fun v : G × (Bool × Bool) => v.2 = (true, false)), qtPush v (εsel v)) +
    s.C false + s.R true

/-! ### Sanity tests -/

example (A B : Finset G) (g : G) (a : A) (b : B) : qtPhi A B (g, (false, false)) a b = (g, a, b) := by
  simp [qtPhi]

example (A B : Finset G) (g : G) (a : A) (b : B) :
    qtPhi A B (g, (true, true)) a b = ((a : G)⁻¹ * g * (b : G)⁻¹, a, b) := by
  simp [qtPhi]

example {A B : Finset G} (v : G × (Bool × Bool)) : qtPush v (0 : A × B → ZMod 2) = 0 := by
  funext q
  simp [qtPush]

example {A B : Finset G} (v : G × (Bool × Bool)) (c : A × B → ZMod 2) :
    qtLocalView (qtPush v c) v = c := by
  funext ab
  simp [qtLocalView, qtPush, qtPhi]

example {A B : Finset G} (CA : Submodule (ZMod 2) (A → ZMod 2)) (CB : Submodule (ZMod 2) (B → ZMod 2))
    (ε : ℝ) (s : SeqDecState (G × A × B)) : ¬ SeqDecStep CA CB ε ⟨s.C, s.R, 0⟩ s :=
  fun h => h.1 rfl

end QAlgorithms


