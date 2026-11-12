-- Prove2me | Definitions.Def_OddOrder_Peterfalvi_S06_CertainHypothesis46
-- name    : OddOrder_Peterfalvi_S06_CertainHypothesis46
-- status  : Definition
-- author  : @burkh4rt
-- created : 2026-11-12T05:46:24.743206+00:00
-- url     : https://prove2.me/theorems/fe4711ab-dcf0-48d7-b7af-3f2fc96f6ba8
-- title:
--   Peterfalvi Hypothesis (4.6): the certain-type Dade configuration in an ambient group
-- statement:
--   Formalizes Peterfalvi Hypothesis (4.6) (§4, pp. 21–24), the running hypothesis for Theorems (4.7)–(4.9) and for the §8 coherence capstone (6.8)(c2). It layers on top of the certain-type structure (4.2) for $L$ and the §4 Dade datum on $A$; for instance (4.6.b) is the TI-cyclic Hypothesis (3.1) for the ambient group $G$, so that the $\sigma$-isometry lands in $\mathrm{Irr}(G)$ rather than only $\mathrm{Irr}(L)$.
--
--   Main definitions: `Hypothesis46Core` (the Dade-free core), `Hypothesis46` (the full Hypothesis (4.6), extending the certain-type structure) and `Hypothesis46.toCore` (forget the Dade data to obtain the core).
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S06_CertainHypothesis46.lean

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S06_CertainHypothesis46.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S06_DadeIsometryCertain
import Definitions.Def_OddOrder_Peterfalvi_S05_TICyclic
import Definitions.Def_OddOrder_GroupTheory_ConjClassSet

namespace OddOrder.Peterfalvi.S06

open OddOrder.RepresentationTheory

variable {G : Type*} [Group G] [Fintype G]

/-- **Peterfalvi Hypothesis (4.6), Dade-free core** (issue 9081).  The structural part of
Hypothesis (4.6): the certain-type structure (4.2) for `↥L` (the parent `Hypothesis ↥L`), the
ambient TI-cyclic data (4.6.b), the normal subgroup `H` with `W₂ ⊆ H ⊆ K` (4.6.c), the covering
condition (4.6.d), and the lightweight normalization `L_normalizes_A` — **without** the §4 Dade
data (`dade`, `dade0`, `τ`) of the full `Hypothesis46`.

This is the exact input type of the (4.7) support chain and the (4.8) conclusion-(1) engine
(`certainType_diff_supp_subset_A0`), none of which project the Dade fields; typing them here keeps
the Dade construction (in the §8/§15/§16 instantiations, a deep FT-support pin) out of their axiom
closure.  The Dade-consuming §6 statements ((4.8) step (4) onward) stay on `Hypothesis46`; use
`Hypothesis46.toCore` to feed them the shared core. -/
structure Hypothesis46Core (A : Set G) (L : Subgroup G) [Fintype ↥L]
    extends Hypothesis ↥L where
  /-- `A` is closed under `L`-conjugation (the single consequence of the (4.6.d) Dade datum the
  (4.7) support chain uses; supplied by `dade.L_normalizes_A` in the full (4.6)). -/
  L_normalizes_A : ∀ (l : ↥L) ⦃a : G⦄, a ∈ A → (l : G) * a * (l : G)⁻¹ ∈ A
  /-- (4.6.b): the ambient TI-cyclic Hypothesis (3.1) for `(G, W)`. -/
  tic : OddOrder.Peterfalvi.S05.TICyclicHypothesis G
  /-- `W₁` of (3.1) is the image of the certain-type `W₁ ≤ ↥L` under `L ↪ G`. -/
  tic_W1 : tic.W1 = toHypothesis.W1.map L.subtype
  /-- `W₂` of (3.1) is the image of the certain-type `W₂ ≤ ↥L` under `L ↪ G`. -/
  tic_W2 : tic.W2 = toHypothesis.W2.map L.subtype
  /-- (4.6.b): the TI-subset `V` of the ambient Hypothesis (3.1) is `W − (W₁ ∪ W₂)` (see
  `Hypothesis46.tic_V`). -/
  tic_V : tic.V = (↑tic.W : Set G) \ ((↑tic.W1 : Set G) ∪ (↑tic.W2 : Set G))
  /-- (4.6.c): a normal subgroup `H ⊴ L`. -/
  subH : Subgroup ↥L
  subH_normal : subH.Normal
  /-- (4.6.c): `W₂ ⊆ H`. -/
  W2_le_subH : toHypothesis.W2 ≤ subH
  /-- (4.6.c): `H ⊆ K`. -/
  subH_le_K : subH ≤ toHypothesis.K
  /-- (4.6.d): every nontrivial element of every `C_K(h)` (`h ∈ H^#`) lies in `A`
  (the covering `⋃_{h∈H^#} C_K(h)^# ⊆ A`). -/
  A_covers : ∀ (hh : ↥L), hh ∈ subH → hh ≠ 1 →
    ∀ (x : ↥L), x ∈ Subgroup.centralizer ({hh} : Set ↥L) ⊓ toHypothesis.K →
      x ≠ 1 → (L.subtype x) ∈ A

/-- **Peterfalvi Hypothesis (4.6).**  See the module docstring.  Extends the certain-type Dade
hypothesis `CertainTypeHypothesis A L` (= (4.2) for `↥L` + §4 Dade on `A`) with the ambient
TI-cyclic
data (3.1), the normal subgroup `H` with `W₂ ⊆ H ⊆ K`, the covering condition on `A`, and the Dade
isometry `τ` relative to `A₀ = A ∪ V^L`.  The Dade-free structural part is `Hypothesis46Core`
(`Hypothesis46.toCore`). -/
structure Hypothesis46 (A : Set G) (L : Subgroup G) [Fintype ↥L]
    [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)]
    extends CertainTypeHypothesis A L where
  /-- (4.6.b): the ambient TI-cyclic Hypothesis (3.1) for `(G, W)`. -/
  tic : OddOrder.Peterfalvi.S05.TICyclicHypothesis G
  /-- `W₁` of (3.1) is the image of the certain-type `W₁ ≤ ↥L` under `L ↪ G`. -/
  tic_W1 : tic.W1 = (toCertainTypeHypothesis.W1).map L.subtype
  /-- `W₂` of (3.1) is the image of the certain-type `W₂ ≤ ↥L` under `L ↪ G`. -/
  tic_W2 : tic.W2 = (toCertainTypeHypothesis.W2).map L.subtype
  /-- (4.6.b): the TI-subset `V` of the ambient Hypothesis (3.1) is `W − (W₁ ∪ W₂)` (viewed in `G`
  via `L ↪ G`) — the (3.1) exceptional set (Coq `cyclicTIset`).  Note this is *smaller* than the
  (4.3.a) `L`-side TI-subset `W − W₂`: only `W − (W₁ ∪ W₂)` is TI in the ambient `G` (in the §8/§10
  instantiations the `W₁^#`-elements have centralizers reaching outside `N_G(A)`, cf. (8.10)/(8.15)
  where `A₀(M) = A(M) ∪ V^M` with this `V`; issue 9004). -/
  tic_V : tic.V = (↑tic.W : Set G) \ ((↑tic.W1 : Set G) ∪ (↑tic.W2 : Set G))
  /-- (4.6.c): a normal subgroup `H ⊴ L`. -/
  subH : Subgroup ↥L
  subH_normal : subH.Normal
  /-- (4.6.c): `W₂ ⊆ H`. -/
  W2_le_subH : toCertainTypeHypothesis.W2 ≤ subH
  /-- (4.6.c): `H ⊆ K`. -/
  subH_le_K : subH ≤ toCertainTypeHypothesis.K
  /-- (4.6.d): every nontrivial element of every `C_K(h)` (`h ∈ H^#`) lies in `A`
  (the covering `⋃_{h∈H^#} C_K(h)^# ⊆ A`). -/
  A_covers : ∀ (hh : ↥L), hh ∈ subH → hh ≠ 1 →
    ∀ (x : ↥L), x ∈ Subgroup.centralizer ({hh} : Set ↥L) ⊓ toCertainTypeHypothesis.K →
      x ≠ 1 → (L.subtype x) ∈ A
  /-- (4.6.d): the §4 Dade datum on the enlarged set `A₀ = A ∪ V^L`, where
  `V^L = conjClassSetIn L tic.V` is the set of `L`-conjugates of the TI-subset `V` of (3.1)
  (Coq `class_support`; the same closure the (8.10) `typePA0` uses, so the §10 instantiation
  aligns definitionally). -/
  dade0 : OddOrder.Peterfalvi.S04.Hypothesis G
    (A ∪ OddOrder.GroupTheory.conjClassSetIn L tic.V) L
  /-- (4.6.e): the Dade isometry `τ` relative to `A₀`. -/
  tau : OddOrder.Peterfalvi.S04.FullDadeIsometryData (G := G) dade0

/-- The Dade-free core of a full Hypothesis (4.6): forget `dade`/`dade0`/`τ`, keeping the
structural (4.2)+(4.6.b-d) data; the normalization `L_normalizes_A` is the one consequence of
the `A`-Dade datum the (4.7) chain uses.  `@[reducible]` so that instance arguments and
statements over `h.toCore` unify with the `h`-forms (`h.toCore.K ≡ h.K` etc.). -/
@[reducible] def Hypothesis46.toCore {A : Set G} {L : Subgroup G} [Fintype ↥L]
    [Invertible (Nat.card G : ℂ)] [Invertible (Nat.card ↥L : ℂ)]
    (h : Hypothesis46 A L) : Hypothesis46Core A L where
  toHypothesis := h.toCertainTypeHypothesis.toHypothesis
  L_normalizes_A := h.dade.L_normalizes_A
  tic := h.tic
  tic_W1 := h.tic_W1
  tic_W2 := h.tic_W2
  tic_V := h.tic_V
  subH := h.subH
  subH_normal := h.subH_normal
  W2_le_subH := h.W2_le_subH
  subH_le_K := h.subH_le_K
  A_covers := h.A_covers

end OddOrder.Peterfalvi.S06


