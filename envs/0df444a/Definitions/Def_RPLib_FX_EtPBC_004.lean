-- Prove2me | Definitions.Def_RPLib_FX_EtPBC_004
-- name    : RPLib_FX_EtPBC_004
-- status  : Definition
-- author  : @Nickrobbins95
-- created : 2026-11-25T16:16:52.363481+00:00
-- url     : https://prove2.me/theorems/edaceb6c-88ff-52d1-9d53-ea83b92fc64d
-- title:
--   Proper base change for the projective line, library file 004
-- statement:
--   File 004 of the proper base change library for the projective line: declarations re-hosted from the following library modules, in dependency order.
--
--   * `S4.Def_RP_EtPBC_A_O2UKd1`: S4-EtPBC-A, O2 M6 (O2UKd1): a global Kummer class along a composite `X₁ ⟶ X ⟶ Y`
--   * `S4.Def_RP_EtPBC_A_O2UKd2`: S4-EtPBC-A, O2 M6 (O2UKd2): the local value of a global Kummer class
--   * `S4.Def_RP_EtPBC_A_O2PPTc`: S4-EtPBC-A, O2 GLOB (O2PPTc): transfer of a piece Kummer class along a shrink `D₁ ⟶ D`
--   * `S4.Def_RP_EtPBC_A_O2Gl2d`: S4-EtPBC-A, O2 GLOB (O2Gl2d): stage S4, the global unit `H` seen on `W₂`
--   * `S4.Def_RP_EtPBC_A_O2Gl2g`: S4-EtPBC-A, O2 GLOB (O2Gl2g): stage S4, the data `e`, `g`, `hHp`, `hHq` of `uk_diff` (pure algebra)
--   * `S4.Def_RP_EtPBC_A_O2Gl2k`: S4-EtPBC-A, O2 GLOB (O2Gl2k): stage S4 with `H` and `D₂ := (D₁)_{φ₁ c₀'}` fixed
--   * `S4.Def_RP_EtPBC_A_O2Gl3b`: S4-EtPBC-A, O2 GLOB (O2Gl3b): the point over `z` on a chart (inputs `χ`, `hχ`, `ht`, `hd` of `uk_diff`)
--   * `S4.Def_RP_EtPBC_A_O2Gl3c`: S4-EtPBC-A, O2 GLOB (O2Gl3c): a piece of `W₁` survives in `W₂ = W₁[1/φ₁ c₀']`
--   * `S4.Def_RP_EtPBC_A_O2UKd3`: S4-EtPBC-A, O2 M6 (O2UKd3): a global Kummer class with local value 0
--   * `S4.Def_RP_EtPBC_A_O2T4e`: S4-EtPBC-A, O2 S5d (O2T4e): `clsD_addF`, `clsD_graph`
--   * `S4.Def_RP_EtPBC_A_O2T5`: S4-EtPBC-A, O2 S5e: splitting off finitely many disjoint sections
--   * `S4.Def_RP_EtPBC_A_O2Gd`: S4-EtPBC-A, O2 M6 (O2Gd): one-point classes at a GOOD point are sums of point classes
--   * `S4.Def_RP_EtPBC_A_O2Gl1d`: S4-EtPBC-A, O2 GLOB (O2Gl1d): transfer of `u` to the shrunk chart, CRT ideals at the bad points
--   * `S4.Def_RP_EtPBC_A_O2PP4a`: S4-EtPBC-A, O2 PP' (O2PP4a): generic glue for the S1 layer
--   * `S4.Def_RP_EtPBC_A_O2Rel4`: S4-EtPBC-A, O2 REL (O2Rel4): the chart at a bad point and the CRT ideals
--   * `S4.Def_RP_EtPBC_A_O2PP3a`: S4-EtPBC-A, O2 PP' (O2PP3a): stages S2-S3 on the charts with `J` = the bad points
--   * `S4.Def_RP_EtPBC_A_O2PP1`: S4-EtPBC-A, O2 PP' (O2PP1): the core of PP' at the chart `D₁` (after stages S2-S3)
--   * `S4.Def_RP_EtPBC_A_O2PP2`: S4-EtPBC-A, O2 PP' (O2PP2): PP' at the chart `D₁` with `G` generic (instances and `D₂` data built here)
--   * `S4.Def_RP_EtPBC_A_O2Gl1a`: S4-EtPBC-A, O2 GLOB (O2Gl1a): residue density at the special point
--   * `S4.Def_RP_EtPBC_A_O2PP4d`: S4-EtPBC-A, O2 PP' (O2PP4d): PP' at `D` through a chart `dm : D₁ ⟶ D` (generic `D₁`)
--   * `S4.Def_RP_EtPBC_A_O2PP5a`: S4-EtPBC-A, O2 PP' (O2PP5a): an `IsLoc` class at `c(a)` comes from a domain chart over a fixed cofinite `U₀`
--   * `S4.Def_RP_EtPBC_A_O2PP4f`: S4-EtPBC-A, O2 PP' (O2PP4f): PP' at a chart `D` for a piece `p` and a Kummer radical `α`
--   * `S4.Def_RP_EtPBC_A_O2Mob`: S4-EtPBC-A, O2 Mob: charts of `P¹` missing one moved point at infinity
--   * `S4.Def_RP_EtPBC_A_O2L1a`: S4-EtPBC-A, L1a (MVr combinatorics): exactness of the free MV complex fibrewise over `C`
--   * `S4.Def_RP_EtPBC_A_O2TB2b`: S4-EtPBC-A, L3b (TB2b): `tauApp2` and the KEY section identity `secMap_pull`
--   * `S4.Def_RP_EtPBC_A_O2TB3`: S4-EtPBC-A, L3 (TB3): pullback of classes `pullH` and base change of `thetaM`
--   * `S4.Def_RP_EtPBC_A_O2L2x`: S4-EtPBC-A, L2x (PullH extras): `pullH` along composites and along etale maps
--   * `S4.Def_RP_EtPBC_A_O2L5a`: S4-EtPBC-A, L5a (Geo1): the horizontal section through a closed point of `P¹_K`
--   * `S4.Def_RP_EtPBC_A_O2L5b`: S4-EtPBC-A, L5b (Geo2): the graph-open `D̃ ⊆ W ×_P Z` and its fibre lemma
--   * `S4.Def_RP_EtPBC_A_O2L7a`: S4-EtPBC-A, O2 L7a: pullback along an isomorphism is an equivalence; germ images are subgroups
--
--   **Formalization note.** One file of a library formalizing proper base change for the projective line: for a noetherian scheme $S$ locally of finite type over an algebraically closed field $K$, the projection $\pi : \mathbf P^1_S \to S$ and a $K$-point $s$ of $S$, the stalk of $R^q \pi_* F$ at $s$ is the étale cohomology $H^q(\mathbf P^1_s, F|_{\mathbf P^1_s})$ of the fibre, for sheaves of $\Lambda$-modules with $\ell^m \Lambda = 0$ and $\ell$ invertible in $K$. The declarations of each library module are re-hosted verbatim (with that module's own `namespace` / `open` / `variable` lines) inside one `section` ... `end` per module, in dependency order; declarations no later result uses are left out. They are definitions together with proved lemmas (no `sorry`), so that later files and solution files can import them.
-- source:
--   SGA 4, Exposé XII (M. Artin, théorème de changement de base pour un morphisme propre), Lecture Notes in Math. 305, Springer (1973); J. S. Milne, Étale Cohomology, Princeton University Press (1980), Chapter VI, §2 (the proper base change theorem) and §1 (cohomology of curves); P. Deligne, Cohomologie étale (SGA 4½), « Arcata », Chapter IV

import Mathlib

/-!
# Proper base change for the projective line, library file 004

Declarations of the formalization of proper base change for the étale cohomology of the projective
line over a base (geometric stalks of the higher direct images of P¹_S → S are the étale cohomology of
the geometric fibres), re-hosted declaration by declaration from the library modules below. Each module
contributes the declarations assigned to this file, copied verbatim with the module's own `namespace` /
`open` / `variable` lines, inside its own `section` ... `end`:

* `S4.Def_RP_EtPBC_A_O2UKd1`: S4-EtPBC-A, O2 M6 (O2UKd1): a global Kummer class along a composite `X₁ ⟶ X ⟶ Y`
* `S4.Def_RP_EtPBC_A_O2UKd2`: S4-EtPBC-A, O2 M6 (O2UKd2): the local value of a global Kummer class
* `S4.Def_RP_EtPBC_A_O2PPTc`: S4-EtPBC-A, O2 GLOB (O2PPTc): transfer of a piece Kummer class along a shrink `D₁ ⟶ D`
* `S4.Def_RP_EtPBC_A_O2Gl2d`: S4-EtPBC-A, O2 GLOB (O2Gl2d): stage S4, the global unit `H` seen on `W₂`
* `S4.Def_RP_EtPBC_A_O2Gl2g`: S4-EtPBC-A, O2 GLOB (O2Gl2g): stage S4, the data `e`, `g`, `hHp`, `hHq` of `uk_diff` (pure algebra)
* `S4.Def_RP_EtPBC_A_O2Gl2k`: S4-EtPBC-A, O2 GLOB (O2Gl2k): stage S4 with `H` and `D₂ := (D₁)_{φ₁ c₀'}` fixed
* `S4.Def_RP_EtPBC_A_O2Gl3b`: S4-EtPBC-A, O2 GLOB (O2Gl3b): the point over `z` on a chart (inputs `χ`, `hχ`, `ht`, `hd` of `uk_diff`)
* `S4.Def_RP_EtPBC_A_O2Gl3c`: S4-EtPBC-A, O2 GLOB (O2Gl3c): a piece of `W₁` survives in `W₂ = W₁[1/φ₁ c₀']`
* `S4.Def_RP_EtPBC_A_O2UKd3`: S4-EtPBC-A, O2 M6 (O2UKd3): a global Kummer class with local value 0
* `S4.Def_RP_EtPBC_A_O2T4e`: S4-EtPBC-A, O2 S5d (O2T4e): `clsD_addF`, `clsD_graph`
* `S4.Def_RP_EtPBC_A_O2T5`: S4-EtPBC-A, O2 S5e: splitting off finitely many disjoint sections
* `S4.Def_RP_EtPBC_A_O2Gd`: S4-EtPBC-A, O2 M6 (O2Gd): one-point classes at a GOOD point are sums of point classes
* `S4.Def_RP_EtPBC_A_O2Gl1d`: S4-EtPBC-A, O2 GLOB (O2Gl1d): transfer of `u` to the shrunk chart, CRT ideals at the bad points
* `S4.Def_RP_EtPBC_A_O2PP4a`: S4-EtPBC-A, O2 PP' (O2PP4a): generic glue for the S1 layer
* `S4.Def_RP_EtPBC_A_O2Rel4`: S4-EtPBC-A, O2 REL (O2Rel4): the chart at a bad point and the CRT ideals
* `S4.Def_RP_EtPBC_A_O2PP3a`: S4-EtPBC-A, O2 PP' (O2PP3a): stages S2-S3 on the charts with `J` = the bad points
* `S4.Def_RP_EtPBC_A_O2PP1`: S4-EtPBC-A, O2 PP' (O2PP1): the core of PP' at the chart `D₁` (after stages S2-S3)
* `S4.Def_RP_EtPBC_A_O2PP2`: S4-EtPBC-A, O2 PP' (O2PP2): PP' at the chart `D₁` with `G` generic (instances and `D₂` data built here)
* `S4.Def_RP_EtPBC_A_O2Gl1a`: S4-EtPBC-A, O2 GLOB (O2Gl1a): residue density at the special point
* `S4.Def_RP_EtPBC_A_O2PP4d`: S4-EtPBC-A, O2 PP' (O2PP4d): PP' at `D` through a chart `dm : D₁ ⟶ D` (generic `D₁`)
* `S4.Def_RP_EtPBC_A_O2PP5a`: S4-EtPBC-A, O2 PP' (O2PP5a): an `IsLoc` class at `c(a)` comes from a domain chart over a fixed cofinite `U₀`
* `S4.Def_RP_EtPBC_A_O2PP4f`: S4-EtPBC-A, O2 PP' (O2PP4f): PP' at a chart `D` for a piece `p` and a Kummer radical `α`
* `S4.Def_RP_EtPBC_A_O2Mob`: S4-EtPBC-A, O2 Mob: charts of `P¹` missing one moved point at infinity
* `S4.Def_RP_EtPBC_A_O2L1a`: S4-EtPBC-A, L1a (MVr combinatorics): exactness of the free MV complex fibrewise over `C`
* `S4.Def_RP_EtPBC_A_O2TB2b`: S4-EtPBC-A, L3b (TB2b): `tauApp2` and the KEY section identity `secMap_pull`
* `S4.Def_RP_EtPBC_A_O2TB3`: S4-EtPBC-A, L3 (TB3): pullback of classes `pullH` and base change of `thetaM`
* `S4.Def_RP_EtPBC_A_O2L2x`: S4-EtPBC-A, L2x (PullH extras): `pullH` along composites and along etale maps
* `S4.Def_RP_EtPBC_A_O2L5a`: S4-EtPBC-A, L5a (Geo1): the horizontal section through a closed point of `P¹_K`
* `S4.Def_RP_EtPBC_A_O2L5b`: S4-EtPBC-A, L5b (Geo2): the graph-open `D̃ ⊆ W ×_P Z` and its fibre lemma
* `S4.Def_RP_EtPBC_A_O2L7a`: S4-EtPBC-A, O2 L7a: pullback along an isomorphism is an equivalence; germ images are subgroups
-/

set_option autoImplicit false

set_option linter.defProp false

-- ===== S4.Def_RP_EtPBC_A_O2UKd1 =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2UKd1): a global Kummer class along a composite `X₁ ⟶ X ⟶ Y`

Generic (abstract affine schemes) forms of the two facts used by `uk_diff` / `uk_kill_glob` (O2UKd2):
* `resLE_kumG_eq_zero`: a global Kummer class dies along `g` once its radicand is a `d`-th power on every piece;
* **`resLE_kapS_kumD_eq_comp`**: along `f : X₁ ⟶ X`, the piece class `kapS p (kumD α)` (`α ^ d = u`) equals the
  restriction of a global Kummer class `c_Y` of a unit `H` along `g₀ : X ⟶ Y`, when `g₀^* H = u · r_p` on `p`,
  `g₀^* H = r_q` on the other pieces, and every `r_q` becomes a `d`-th power along every `Ψ` compatible with `f`;
* **`resLE_kumG_eq_zero_comp`**: the same class dies along `f` when `g₀^* H = r_q` on every piece.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtPBC

section Aux

theorem appTop_comp' {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : Γ(Z, ⊤)) :
    (f ≫ g).appTop x = f.appTop (g.appTop x) := by
  rw [Scheme.Hom.comp_appTop]
  rfl

end Aux

section KillG

end KillG

section KapDC

end KapDC

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2UKd2 =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2UKd2): the local value of a global Kummer class

Setting of `uk_kill` (O2UK2c). A global Kummer class `c_Y` of a unit `H` on `Y = (T' ×_P R)` (`τ' : T' ⟶ U_o`,
`m : D ×_P U_o ⟶ T'` over `U_o`), with `H = u (1 + t e_p)` on the piece `p` of `W` and `H = 1 + t e_q` on the other
pieces (`e_q` roots of one monic `g ∈ B[X]`, `t` zero at `z`):
* **`uk_diff`**: `ε_loc(D) ∘ θ⁻¹(kapS p (kumD α)) = ε_loc(D) ∘ Λ[m]^*(θ'⁻¹ c_Y)` for `α ^ d = u`;
Proof: `exists_ukChart` (one etale nbhd where every `1 + t e_q` is a `d`-th power), `locCls_shrink`, `theta_natural`
(twice: along `M₁` and along `m`, never along `M₁ ≫ m`), O2UKd1 with `exists_pow_of_uk`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtPBC

section GenUKD

universe w' v₀ u₀ v₁ u₁ v₂ u₂ v₃ u₃

variable {C' : Type u₀} [Category.{v₀} C'] [Abelian C'] {hC : HasExt.{w'} C'}
  {D₁ : Type u₁} [Category.{v₁} D₁] [Abelian D₁] {h₁ : HasExt.{w'} D₁}
  {D₂ : Type u₂} [Category.{v₂} D₂] [Abelian D₂] {h₂ : HasExt.{w'} D₂}
  {D₃ : Type u₃} [Category.{v₃} D₃] [Abelian D₃] {h₃ : HasExt.{w'} D₃}

/-- Generic form of `uk_diff` (kept generic so the kernel never re-checks concrete `Ext` instances). -/
theorem uk_diff_gen {Z X₁ X X' F : C'} {U₁ V₁ : D₁} {U V : D₂} {U' V' : D₃}
    (E : Ext.{w'} Z X 1) (E₁ : Ext.{w'} Z X₁ 1) (u₁ : X₁ ⟶ X) (u : X ⟶ X')
    (hs : ∀ κ : Ext.{w'} X F 1, E.comp κ (show 1 + 1 = 2 from rfl) =
      E₁.comp ((Ext.mk₀ u₁).comp κ (zero_add 1)) (show 1 + 1 = 2 from rfl))
    (θ₁ : Ext.{w'} X₁ F 1 ≃+ Ext.{w'} U₁ V₁ 1) (θ : Ext.{w'} X F 1 ≃+ Ext.{w'} U V 1)
    (θ' : Ext.{w'} X' F 1 ≃+ Ext.{w'} U' V' 1)
    (ρ₁ : Ext.{w'} U V 1 → Ext.{w'} U₁ V₁ 1) (ρ : Ext.{w'} U' V' 1 → Ext.{w'} U V 1)
    (hn₁ : ∀ x, θ₁ ((Ext.mk₀ u₁).comp x (zero_add 1)) = ρ₁ (θ x))
    (hn : ∀ x, θ ((Ext.mk₀ u).comp x (zero_add 1)) = ρ (θ' x))
    (K : Ext.{w'} U V 1) (c : Ext.{w'} U' V' 1) (hk : ρ₁ K = ρ₁ (ρ c)) :
    E.comp (θ.symm K) (show 1 + 1 = 2 from rfl) =
      E.comp ((Ext.mk₀ u).comp (θ'.symm c) (zero_add 1)) (show 1 + 1 = 2 from rfl) := by
  rw [hs, hs]
  congr 1
  apply θ₁.injective
  rw [hn₁, hn₁, hn, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, hk]

end GenUKD

section UKd

end UKd

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2PPTc =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2PPTc): transfer of a piece Kummer class along a shrink `D₁ ⟶ D`

GLOB/REL PLAN v1 (5). For a shrink `dm : D₁ ⟶ D` of local-class neighbourhoods of `z` (both with one geometric
point over `z`), with Shapiro isomorphisms `θ` over `opEt Uo`:
* **`locCls_kapS_shrink`**: `ε(D) ∘ θ⁻¹(kapS p (kumD α)) = ε(D₁) ∘ θ₁⁻¹(Σ_{p₁} kapS p₁ (χ₁ p₁))`, where
  `χ₁ p₁ = kumD (γ p₁)` on the pieces of `W₁` over `p` and `0` on the others (`γ p₁ ^ d = u` there).
Proof: `locCls_shrink`, `theta_natural` along `prdMap dm`, `resLE_kapS_kumD_sum` (O2PPTb) along `wm (prdMap dm)`.
* **`piece_eq_of_away`**: under a localization `A → A[1/s]` two minimal primes over the same prime agree (Zariski
  shrinks never split pieces); **`ker_kerMap`**: `ker (kerMap f p₁) = comap f p₁`;
* **`sum_kapS_eq_single`** / **`sum_kapS_eq_zero`**: collapsing `Σ kapS Q (χ Q)` when at most one `χ Q ≠ 0`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtPBC

section Away

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B]

/-- **Pieces never split under a localization `B = A[1/s]`**: two minimal primes of `B` over the same prime `p` agree. -/
theorem piece_eq_of_away (s : A) [IsLocalization.Away s B] {p : Ideal A} [hp : p.IsPrime] {p₁ p₂ : Ideal B}
    (hp₁ : p₁ ∈ minimalPrimes B) (hp₂ : p₂ ∈ minimalPrimes B) (h₁ : p ≤ p₁.comap (algebraMap A B))
    (h₂ : p ≤ p₂.comap (algebraMap A B)) : p₁ = p₂ := by
  have hdis : Disjoint (Submonoid.powers s : Set A) (p : Set A) := by
    rw [Set.disjoint_left]
    rintro x ⟨k, rfl⟩ hx
    have hu : IsUnit (algebraMap A B (s ^ k)) := by
      rw [map_pow]
      exact (IsLocalization.Away.algebraMap_isUnit s).pow k
    have hm : algebraMap A B (s ^ k) ∈ p₁ := h₁ hx
    exact hp₁.1.1.ne_top (Ideal.eq_top_of_isUnit_mem _ hm hu)
  have hpr : (Ideal.map (algebraMap A B) p).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers s) B p hp hdis
  have key : ∀ q : Ideal B, q ∈ minimalPrimes B → p ≤ q.comap (algebraMap A B) →
      q = Ideal.map (algebraMap A B) p := fun q hq hle => by
    have hle' : Ideal.map (algebraMap A B) p ≤ q :=
      (Ideal.map_mono hle).trans (IsLocalization.map_under (Submonoid.powers s) B q).le
    exact le_antisymm (hq.2 ⟨hpr, bot_le⟩ hle') hle'
  exact (key p₁ hp₁ h₁).trans (key p₂ hp₂ h₂).symm

end Away

section KerMap

end KerMap

section Single

end Single

section PPTc

end PPTc

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gl2d =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2Gl2d): stage S4, the global unit `H` seen on `W₂`

GLOB/REL PLAN v1, stage S4 (ring level). `ρ := (wm (prdMap (toDG c hG₀) (opEt U₀))).appTop : Γ(Y₀) → Γ(Y₁)`,
`m := mG c hle D₂ hD₂` (O2Gl2b), `D₂ = chEt c φ₂`, `d : D₂ ⟶ D_{g₀}`:
* `prdMap_comp`, `wm_prdMap_comp_appTop`: `prdMap` is functorial (target an open chart);
* `wm_mG_appTop`: `m^* ∘ ρ = (prdMap d)^*`; `wm_mG_gamMap`: `m^* ρ (r) = bW (φ₂ r)` for `r ∈ k[X]`;
* `exists_Hg`: `H := ũ' t^{-N}` is a unit; **`wm_mG_H`**: `m^* H · bW(φ₂ t)^N = (prdMap d)^* ũ'`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtPBC

section Fun

variable {P : Scheme.{0}}

theorem exists_Hg {A : Type*} [CommRing A] {x b : A} (hx : IsUnit x) (hb : IsUnit b) (N : ℕ) :
    ∃ H : A, IsUnit H ∧ H * b ^ N = x := by
  obtain ⟨u, rfl⟩ := hb
  refine ⟨x * ↑(u⁻¹ ^ N), hx.mul (Units.isUnit _), ?_⟩
  rw [mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_pow, inv_mul_cancel, Units.val_one, mul_one]

end Fun

section H

end H

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gl2g =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2Gl2g): stage S4, the data `e`, `g`, `hHp`, `hHq` of `uk_diff` (pure algebra)

GLOB/REL PLAN v1, stage S4 (ring level, abstract rings). `G₂ = G₁[1/s]` (the Zariski shrink `W₂ → W₁`), `B₁ → G₁`,
`B₂ → G₂`, `ι : B₁ → B₂` compatible, `z ∈ Π_q Frac(G₁ ⧸ q)` integral over `B₁`, `μH T₂^N = x₁` with
`x₁ = T₁^N ũ (1 - T₁ z)` (`ũ = (u₁ on p₁, 1 elsewhere)`):
* `eq_comap_of_le_comap`: below a minimal prime of a localization lies exactly one minimal prime (its contraction);
* `exists_psi`, `psi_unique`, `psi_update`, `psi_update_ne`: the maps `Frac(G₁ ⧸ q₁) → Frac(G₂ ⧸ q)`;
* `exists_monic_he`: one monic `g ∈ B₂[X]` of positive degree killing every `-Ψ_q (z_{q₁})`;
* **`exists_S4_gen`**: `e q := -Ψ_q (z_{q₁ q})` and `g` with `he`, `hHp` (any compatible `Ψ`), `hHq`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

section Below

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A]

/-- Under a localization, a prime below the contraction of a minimal prime is that contraction. -/
theorem eq_comap_of_le_comap (M : Submonoid R) [IsLocalization M A] {q : Ideal A} (hq : q ∈ minimalPrimes A)
    {P : Ideal R} [hP : P.IsPrime] (hle : P ≤ q.comap (algebraMap R A)) : P = q.comap (algebraMap R A) := by
  have hqp : q.IsPrime := hq.1.1
  have hd : Disjoint (M : Set R) (q.comap (algebraMap R A) : Set R) :=
    ((IsLocalization.isPrime_iff_isPrime_disjoint M A q).mp hqp).2
  have hdP : Disjoint (M : Set R) (P : Set R) := Set.disjoint_of_subset_right hle hd
  have hmP : (P.map (algebraMap R A)).IsPrime := IsLocalization.isPrime_of_isPrime_disjoint M A P hP hdP
  have hge : q ≤ P.map (algebraMap R A) := hq.2 ⟨hmP, bot_le⟩ (Ideal.map_le_iff_le_comap.mpr hle)
  refine le_antisymm hle ?_
  calc q.comap (algebraMap R A) ≤ (P.map (algebraMap R A)).comap (algebraMap R A) := Ideal.comap_mono hge
    _ = P := IsLocalization.under_map_of_isPrime_disjoint M A hP hdP

end Below

section Psi

variable {G₁ G₂ : Type} [CommRing G₁] [CommRing G₂]

/-- The map `Frac(G₁ ⧸ P) → Frac(G₂ ⧸ Q)` when `Q ∩ G₁ = P`. -/
theorem exists_psi (σ : G₁ →+* G₂) (P : Ideal G₁) [P.IsPrime] (Q : Ideal G₂) [Q.IsPrime] (h : Q.comap σ = P) :
    ∃ Ψ : FractionRing (G₁ ⧸ P) →+* FractionRing (G₂ ⧸ Q),
      ∀ a : G₁, Ψ (algebraMap _ _ (Ideal.Quotient.mk P a)) = algebraMap _ _ (Ideal.Quotient.mk Q (σ a)) := by
  have hinj : Function.Injective ((algebraMap (G₂ ⧸ Q) (FractionRing (G₂ ⧸ Q))).comp
      (Ideal.quotientMap Q σ h.ge)) :=
    (IsFractionRing.injective _ _).comp (Ideal.quotientMap_injective' h.le)
  exact ⟨IsFractionRing.lift hinj, fun a => (IsFractionRing.lift_algebraMap hinj _).trans
    (congrArg (algebraMap (G₂ ⧸ Q) (FractionRing (G₂ ⧸ Q)))
      (Ideal.quotientMap_mk (I := Q) (f := σ) (H := h.ge) (x := a)))⟩

/-- Maps out of `Frac(G₁ ⧸ P)` are determined on `G₁`. -/
theorem psi_unique (P : Ideal G₁) {K : Type} [CommRing K] {Ψ Ψ' : FractionRing (G₁ ⧸ P) →+* K}
    (h : ∀ a : G₁, Ψ (algebraMap _ _ (Ideal.Quotient.mk P a)) = Ψ' (algebraMap _ _ (Ideal.Quotient.mk P a))) :
    Ψ = Ψ' :=
  IsLocalization.ringHom_ext (nonZeroDivisors (G₁ ⧸ P)) (Ideal.Quotient.ringHom_ext (RingHom.ext h))

end Psi

section Monic

end Monic

section S4Gen

end S4Gen

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gl2k =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2Gl2k): stage S4 with `H` and `D₂ := (D₁)_{φ₁ c₀'}` fixed

GLOB/REL PLAN v1, stage S4. From the S2-S3 output (`y ∣ c₀ = t^{e₀} c₀'`, `hy`, `hz`) and `G := g₀ c₀' t`:
* **`isUnit_locF_of_dvd_pow`**, **`dvd_G_pow`**: `c₀` and `t` are units of `k[X]_G`;
* **`exists_S4H`**: a unit `H` on `Y_G` with `H ρ(t)^N = ρ(y)` (`isUnit_rho`, `exists_Hg`) and the `e`, `g`, `he`, `hHp`, `hHq`
  of `uk_diff` on `D₂ = chEt c (φ₁ ≫ locF (φ₁ c₀'))` with `d₂₁ = toDF` (`exists_S4`, `isLocalization_away_toDF`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

open scoped nonZeroDivisors

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtPBC

section Units

variable {k : Type} [Field k]

theorem dvd_G_pow (g₀ c₀' : k[X]) (a : k) (e₀ : ℕ) :
    (X - C a) ^ e₀ * c₀' ∣ (g₀ * c₀' * (X - C a)) ^ (e₀ + 1) := by
  rw [pow_succ]
  exact mul_dvd_mul (pow_dvd_pow_of_dvd (dvd_mul_left (X - C a) (g₀ * c₀')) e₀)
    ((dvd_mul_left c₀' g₀).mul_right (X - C a))

end Units

section ToDF

end ToDF

section S4H

end S4H

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gl3b =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2Gl3b): the point over `z` on a chart (inputs `χ`, `hχ`, `ht`, `hd` of `uk_diff`)

For a chart `chEt c φ` with a fibre point `n` over `z = c(a)`:
* **`fpt_mem_t`**: `φ (X - C a)` lies in the prime of `n`;
* **`exists_chi`**: the residue map `χ : B → κ(n)` with `χ(φ t) = 0` and `(chEt c φ).hom ⟨ker χ⟩ = z`;
* **`isUnit_natCast_of_prim`**: `d ∣ N`, `ζ0 ∈ k` a primitive `N`-th root ⇒ `d` is a unit of `B`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtPBC

section ZPt

variable {k : Type} [Field k] {P : Scheme.{0}} {a : k} {B : CommRingCat.{0}} (φ : CommRingCat.of k[X] ⟶ B)

include φ in
theorem isUnit_natCast_of_prim {N d : ℕ} [NeZero N] {ζ0 : k} (hζ0 : IsPrimitiveRoot ζ0 N) (hdN : d ∣ N) :
    IsUnit ((d : ℕ) : B) := by
  have hN : ((N : ℕ) : k) ≠ 0 := hζ0.neZero'.out
  obtain ⟨m, hm⟩ := hdN
  have hd : ((d : ℕ) : k) ≠ 0 := fun h => hN (by rw [hm, Nat.cast_mul, h, zero_mul])
  have h1 : IsUnit (C ((d : ℕ) : k) : k[X]) := Polynomial.isUnit_C.2 (isUnit_iff_ne_zero.2 hd)
  have h2 := h1.map φ.hom
  rwa [map_natCast C, map_natCast] at h2

end ZPt

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gl3c =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2Gl3c): a piece of `W₁` survives in `W₂ = W₁[1/φ₁ c₀']`

* **`exists_piece_overB`** (generic): in a localization `G₂ = G₁[1/s]`, a minimal prime `p₁ ∌ s` lies under a minimal
  prime `p₂` (`p₁ ≤ ker (κ p₂)` for any `κ` with `ker (κ q) = σ⁻¹ q`);
* **`not_mem_of_toPiQ_ne_zero`**; **`exists_piece_toDF`**: the chart form (`c₀' ≠ 0`, flatness of `W₁ → Spec k[X]`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtPBC

section PieceOver

variable {G₁ G₂ : Type} [CommRing G₁] [CommRing G₂]

theorem exists_piece_overB (σ : G₁ →+* G₂) (s : G₁) (hloc : letI := σ.toAlgebra; IsLocalization.Away s G₂)
    (κ : ∀ q : minimalPrimes G₂, G₁ →+* G₂ ⧸ q.1) (hκ : ∀ q, RingHom.ker (κ q) = Ideal.comap σ q.1)
    (p₁ : minimalPrimes G₁) (hs : s ∉ p₁.1) : ∃ p₂ : minimalPrimes G₂, p₁.1 ≤ RingHom.ker (κ p₂) := by
  let _ : Algebra G₁ G₂ := σ.toAlgebra
  have _ := hloc
  have hp : p₁.1.IsPrime := p₁.2.1.1
  have hd : Disjoint (Submonoid.powers s : Set G₁) p₁.1 := (Ideal.disjoint_powers_iff_notMem_of_isPrime s).2 hs
  have hu : (p₁.1.map (algebraMap G₁ G₂)).under G₁ = p₁.1 :=
    IsLocalization.under_map_of_isPrime_disjoint (Submonoid.powers s) G₂ hp hd
  have hmin : p₁.1.map (algebraMap G₁ G₂) ∈ minimalPrimes G₂ := by
    have e := IsLocalization.minimalPrimes_map (Submonoid.powers s) G₂ (⊥ : Ideal G₁)
    rw [Ideal.map_bot] at e
    show p₁.1.map (algebraMap G₁ G₂) ∈ (⊥ : Ideal G₂).minimalPrimes
    rw [e]
    show (p₁.1.map (algebraMap G₁ G₂)).under G₁ ∈ (⊥ : Ideal G₁).minimalPrimes
    rw [hu]
    exact p₁.2
  refine ⟨⟨_, hmin⟩, ?_⟩
  rw [hκ]
  exact hu.ge

end PieceOver

section PieceChart

end PieceChart

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2UKd3 =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2UKd3): a global Kummer class with local value 0

Setting of `uk_kill` (O2UK2c). A global Kummer class `c_Y` of a unit `H` on `Y = (T' ×_P R)` (`τ' : T' ⟶ U_o`,
`m : D ×_P U_o ⟶ T'` over `U_o`), with `H = u (1 + t e_p)` on the piece `p` of `W` and `H = 1 + t e_q` on the other
pieces (`e_q` roots of one monic `g ∈ B[X]`, `t` zero at `z`):
* **`uk_kill_glob`**: `ε_loc(D) ∘ Λ[m]^*(θ'⁻¹ c_Y) = 0` when `H = 1 + t e_q` on every piece.
Proof: `exists_ukChart` (one etale nbhd where every `1 + t e_q` is a `d`-th power), `locCls_shrink`, `theta_natural`
(twice: along `M₁` and along `m`, never along `M₁ ≫ m`), O2UKd1 with `exists_pow_of_uk`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtPBC

section GenUKK

universe w' v₀ u₀ v₁ u₁ v₂ u₂ v₃ u₃

variable {C' : Type u₀} [Category.{v₀} C'] [Abelian C'] {hC : HasExt.{w'} C'}
  {D₁ : Type u₁} [Category.{v₁} D₁] [Abelian D₁] {h₁ : HasExt.{w'} D₁}
  {D₂ : Type u₂} [Category.{v₂} D₂] [Abelian D₂] {h₂ : HasExt.{w'} D₂}
  {D₃ : Type u₃} [Category.{v₃} D₃] [Abelian D₃] {h₃ : HasExt.{w'} D₃}

/-- Generic form of `uk_kill_glob` (kept generic so the kernel never re-checks concrete `Ext` instances). -/
theorem uk_kill_gen {Z X₁ X X' F : C'} {U₁ V₁ : D₁} {U V : D₂} {U' V' : D₃}
    (E : Ext.{w'} Z X 1) (E₁ : Ext.{w'} Z X₁ 1) (u₁ : X₁ ⟶ X) (u : X ⟶ X')
    (hs : ∀ κ : Ext.{w'} X F 1, E.comp κ (show 1 + 1 = 2 from rfl) =
      E₁.comp ((Ext.mk₀ u₁).comp κ (zero_add 1)) (show 1 + 1 = 2 from rfl))
    (θ₁ : Ext.{w'} X₁ F 1 ≃+ Ext.{w'} U₁ V₁ 1) (θ : Ext.{w'} X F 1 ≃+ Ext.{w'} U V 1)
    (θ' : Ext.{w'} X' F 1 ≃+ Ext.{w'} U' V' 1)
    (ρ₁ : Ext.{w'} U V 1 → Ext.{w'} U₁ V₁ 1) (ρ : Ext.{w'} U' V' 1 → Ext.{w'} U V 1)
    (hn₁ : ∀ x, θ₁ ((Ext.mk₀ u₁).comp x (zero_add 1)) = ρ₁ (θ x))
    (hn : ∀ x, θ ((Ext.mk₀ u).comp x (zero_add 1)) = ρ (θ' x))
    (c : Ext.{w'} U' V' 1) (hz : ρ₁ (ρ c) = 0) :
    E.comp ((Ext.mk₀ u).comp (θ'.symm c) (zero_add 1)) (show 1 + 1 = 2 from rfl) = 0 := by
  rw [hs]
  have h0 : (Ext.mk₀ u₁).comp ((Ext.mk₀ u).comp (θ'.symm c) (zero_add 1)) (zero_add 1) = 0 := by
    apply θ₁.injective
    rw [hn₁, hn, AddEquiv.apply_symm_apply, hz, map_zero]
  rw [h0, Ext.comp_zero]

end GenUKK

section UKd

end UKd

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2T4e =====
section

/-!
# S4-EtPBC-A, O2 S5d (O2T4e): `clsD_addF`, `clsD_graph`
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtPBC

universe u

section GenAddF
universe w v₁ u₁ v₂ u₂ v₃ u₃
variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {hC : HasExt.{w} C}
  {D : Type u₂} [Category.{v₂} D] [Abelian D] {hD : HasExt.{w} D}
  {D' : Type u₃} [Category.{v₃} D'] [Preadditive D']

theorem cls_addF_gen (R : D' ⥤ D) [R.Additive] {G Z : D'} (f f' : G ⟶ Z) {W X0 : D} (c : R.obj Z ⟶ W)
    (Y : Ext.{w} X0 (R.obj G) 1) {A0 A1 B : C} (A : Ext.{w} A0 A1 1) (e : Ext.{w} A1 B 1 ≃+ Ext.{w} X0 W 1) :
    A.comp (e.symm (Y.comp (Ext.mk₀ (R.map (f + f') ≫ c)) (add_zero 1))) (show 1 + 1 = 2 from rfl) =
      A.comp (e.symm (Y.comp (Ext.mk₀ (R.map f ≫ c)) (add_zero 1))) (show 1 + 1 = 2 from rfl) +
      A.comp (e.symm (Y.comp (Ext.mk₀ (R.map f' ≫ c)) (add_zero 1))) (show 1 + 1 = 2 from rfl) := by
  rw [R.map_add, Preadditive.add_comp, Ext.mk₀_add, Ext.comp_add, map_add, Ext.comp_add]

end GenAddF

section Split

end Split

section Graph

end Graph

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2T5 =====
section

/-!
# S4-EtPBC-A, O2 S5e: splitting off finitely many disjoint sections

* `secLiftOI g σ h`: a section `σ` of `N` lifted through an open immersion `g : R ⟶ N` containing its range;
* **`clsD_splitAll`**: for sections `σ i` (`i ∈ S`, a finset) of a separated etale `N` over `D = Spec B` with
  pairwise disjoint ranges, `clsD f Y` is a sum of section summands `clsD (Λ[σ i] ≫ f) Y'` plus one residual
  summand `clsD (Λ[g] ≫ f) Y_R` through an open immersion `g : R ⟶ N` missing every range `σ i`, `i ∈ S`;
  `R` is affine when `N` is (`isAffine_opn_secV`: section ranges are clopen).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtPBC

universe u

section LiftOI

end LiftOI

section Aff

variable {X : Scheme.{u}}

/-- An open immersion with closed range into an affine scheme has affine source. -/
theorem isAffine_of_isClosed_range {Y : Scheme.{u}} (j : Y ⟶ X) [IsOpenImmersion j] [IsAffine X]
    (h : IsClosed (Set.range j)) : IsAffine Y := by
  have := IsClosedImmersion.of_isPreimmersion j h
  exact isAffine_of_isAffineHom j

end Aff

section SplitAll

end SplitAll

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gd =====
section

/-!
# S4-EtPBC-A, O2 M6 (O2Gd): one-point classes at a GOOD point are sums of point classes

* `graph_left_eq_of_fib`: sections with the same value at a geometric point have meeting graphs there;
* `mem_graph_of_card`: if disjoint graphs of sections `τ i : W ⟶ T` are at least as many as the points of every
  geometric fibre of `T` (finite), every point of `W ×_P T` lies on one of the graphs;
* `isZero_freeSh_of_isEmpty`, `ext_eq_zero_of_isZero`;
* **`isLoc_free_good`**: for `T` quasi-compact separated etale over `P` and `z = c (X = a)` a point where the fibre of
  `T` is as large as any fibre (a good point: constant degree near `z`), every one-point class at `z` with
  coefficients `Λ[T]` is in the subgroup generated by the point classes `PtCls` (the residual of `isLoc_free_decomp`
  is EMPTY).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtPBC

universe u w

section GoodGeo

end GoodGeo

section Zero

theorem ext_eq_zero_of_isZero {C : Type*} [Category C] [Abelian C] [HasExt.{w} C] {X Y : C} {n : ℕ}
    (x : Ext.{w} X Y n) (hY : IsZero Y) : x = 0 := by
  rw [← Ext.comp_mk₀_id x, hY.eq_of_src (𝟙 Y) 0, Ext.mk₀_zero, Ext.comp_zero]

end Zero

section GenZero

universe w' v₁ u₁ v₂ u₂ v₃ u₃

end GenZero

section Good

end Good

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gl1d =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2Gl1d): transfer of `u` to the shrunk chart, CRT ideals at the bad points

GLOB/REL PLAN v1, stages S1-S2 (pure algebra).
* `dvd_of_psi`, `psi_ne_zero`, **`exists_pow_mul_psi_pair`**: along `Ψ : Frac(G ⧸ p) →+* Frac A₁` induced by `κ : G →+* A₁`,
  `u = x / y` with `x ∣ c_x`, `y ∣ c_y` and `κ c_x = τ^e w₁`, `κ c_y = τ^e' w₂` (`wᵢ` units) gives
  `τ^(e+e') (Ψ u)^{±1}` integral (the `hj₁`, `hj₂` of `exists_glob_approx`, O2Gl1b);
* `isCoprime_span_map`, `pairwise_isCoprime_X_sub_C`, `isCoprime_X_sub_C_pow_span`: the CRT hypotheses `hJ`, `hJt`
  for `J i = (X - a_i) S`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

section Psi

variable {G A₁ K₁ : Type*} [CommRing G] [CommRing A₁] [IsDomain A₁] [Field K₁] [Algebra A₁ K₁]
  [IsFractionRing A₁ K₁] (p : Ideal G) [p.IsPrime] (κ : G →+* A₁) (Ψ : FractionRing (G ⧸ p) →+* K₁)
  (hΨ : ∀ a, Ψ (algebraMap (G ⧸ p) _ (Ideal.Quotient.mk p a)) = algebraMap A₁ K₁ (κ a))

include hΨ in
theorem dvd_of_psi {y c : G} (hy : Ideal.Quotient.mk p y ∣ Ideal.Quotient.mk p c) : κ y ∣ κ c := by
  obtain ⟨z, hz⟩ := hy
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hmem : c - y * z ∈ p := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hz, sub_self]
  have h0 : κ (c - y * z) = 0 := by
    apply IsFractionRing.injective A₁ K₁
    rw [← hΨ, Ideal.Quotient.eq_zero_iff_mem.2 hmem, map_zero, map_zero, map_zero]
  rw [map_sub, map_mul, sub_eq_zero] at h0
  exact ⟨κ z, h0⟩

include hΨ in
theorem psi_ne_zero {y : G} (hy0 : Ideal.Quotient.mk p y ≠ 0) : κ y ≠ 0 := by
  intro h
  have h1 : Ψ (algebraMap (G ⧸ p) _ (Ideal.Quotient.mk p y)) = 0 := by rw [hΨ, h, map_zero]
  exact hy0 ((map_eq_zero_iff _ (IsFractionRing.injective _ _)).1 ((map_eq_zero_iff Ψ Ψ.injective).1 h1))

end Psi

section CRT

end CRT

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2PP4a =====
section

/-!
# S4-EtPBC-A, O2 PP' (O2PP4a): generic glue for the S1 layer

* `comp_symm_sum_mem`, `comp_symm_dite_mem`, `mem_of_eq_mem`: membership of `ε ∘ θ⁻¹(Σ_i v_i)` in an additive
  subgroup from the summands (the piece sum of the PPT transfer, characters `if p ≤ ker then kumD else 0`);
* `exists_hj_pair`: `hj₁`, `hj₂` of `pp_chart` in `toPiQ` form from `u = x / y`, `x ∣ c_x`, `y ∣ c_y`
  (`exists_pow_mul_psi_pair` along a ring map `σ`), `fracMap_ne_zero`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open CategoryTheory Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtPBC.EtMV

universe w v u

section ExtMem

end ExtMem

theorem mem_of_eq_mem {T : Type*} [AddGroup T] {Gr : AddSubgroup T} {x y : T} (h : x = y) (hy : y ∈ Gr) :
    x ∈ Gr :=
  h ▸ hy

section HJ

variable {G G₁ : Type} [CommRing G] [CommRing G₁] (p : Ideal G) [p.IsPrime] (p₁ : minimalPrimes G₁)
  (σ : G →+* G₁) (Ψ : FractionRing (G ⧸ p) →+* FractionRing (G₁ ⧸ p₁.1))
  (hΨ : ∀ a : G, Ψ (algebraMap _ _ (Ideal.Quotient.mk p a)) = algebraMap _ _ (Ideal.Quotient.mk p₁.1 (σ a)))

theorem fracMap_ne_zero {u : FractionRing (G ⧸ p)} (hu : u ≠ 0) : Ψ u ≠ 0 := by
  have : p₁.1.IsPrime := p₁.2.1.1
  exact (map_ne_zero Ψ).2 hu

end HJ

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Rel4 =====
section

/-!
# S4-EtPBC-A, O2 REL (O2Rel4): the chart at a bad point and the CRT ideals

REL PLAN v2 (s126) + s128 fix. At a bad point `c(b)` (`G = (X - C b)^m G_b`, `G_b(b) ≠ 0`, `c(b) ∉ U₀`), the chart
`D' := D_{G_b} = chEt c (locF G_b)` satisfies the hypotheses of `bad_term_zero'` (O2Bd5):
* fibres: **`subsingleton_fib_of_mono`**, **`nonempty_fib_of_mem`** (generic);
* **`bad_pt`**, **`badCh_r₁`** (`hDr₁`), **`badCh_r`** (`hDr`), **`badCh_D'`** (`hD'`), **`badCh_hUo`**, **`isAffine_badCh`**,
  **`badCh_hta`** (`hta`), **`badCh_n`** (`hDn`);
* CRT ideals `J b := (X - C b) S`: **`span_coprime_pow`** (`hJt`), **`pairwise_span_coprime`** (`hJ`) of `exists_S23_chart`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.EtMV

section Fib

end Fib

section BadCh

end BadCh

section BadCh2

end BadCh2

section JAlg

variable {k : Type} [Field k] {S : Type} [CommRing S] [Algebra k[X] S]

theorem isCoprime_X_sub_C_ne {a b : k} (hab : a ≠ b) : IsCoprime (X - C a) (X - C b) :=
  isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero.2 hab).isUnit

end JAlg

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2PP3a =====
section

/-!
# S4-EtPBC-A, O2 PP' (O2PP3a): stages S2-S3 on the charts with `J` = the bad points

GLOB/REL PLAN v1: `exists_S23B` / `exists_S23_chart` (O2Gl2j) with `t = X - a` and `J_b = (X - b)` for the points
`b` with `p b` (`p b → b ≠ a`), so that no `J`-family has to be built at the chart level (instance paths on
`integralClosure k[X] Γ(Y₀)` built outside the generic lemma made the chart-level unification time out).
* helpers: `ne_zero_right_of_eq`, `dvd_map_of_eq`, `badJ`, `badJ_pairwise`, `badJ_coprime`, `badJ_mem`;
* **`exists_S23B_bad`** (generic rings) and **`exists_S23_chart_bad`** (the chart instance).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Polynomial

open scoped nonZeroDivisors

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.EtMV

section PP3Helpers

theorem ne_zero_right_of_eq {k : Type} [Field k] {c₀ t c₀' : k[X]} (h : c₀ = t * c₀') (h0 : c₀ ≠ 0) : c₀' ≠ 0 := by
  rintro rfl
  exact h0 (by rw [h, mul_zero])

theorem dvd_map_of_eq {A B : Type} [Dvd B] (f : A → B) {y : B} {c₀ c₁ : A} (h : c₀ = c₁) (hd : y ∣ f c₀) :
    y ∣ f c₁ := h ▸ hd

section BadJ

variable {k : Type} [Field k] {S : Type} [CommRing S] [Algebra k[X] S]

/-- The ideals `(X - b)` of `S`, `b` in `{b // p b}` (the `J` of `exists_S23_chart`). -/
def badJ (p : k → Prop) (i : Subtype p) : Ideal S := Ideal.span {algebraMap k[X] S (X - C i.1)}

theorem badJ_mem {p : k → Prop} {b : k} (hb : p b) {x : S} (hx : x ∈ badJ p ⟨b, hb⟩) :
    x ∈ Ideal.span {algebraMap k[X] S (X - C b)} := hx

end BadJ

end PP3Helpers

section S23BBad

end S23BBad

section S23Bad

end S23Bad

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2PP1 =====
section

/-!
# S4-EtPBC-A, O2 PP' (O2PP1): the core of PP' at the chart `D₁` (after stages S2-S3)

GLOB/REL PLAN v1 + REL PLAN v2. With the S2-S3 output (`hdvd`, `hy`, `hzI` of `exists_S23_chart`, `c₀ = t^e₀ c₀'`) and
`G := g₀ c₀' t` kept generic: `exists_S4H'` (O2Bd4) gives `H`, `e`, `g`; `exists_root_of_isUnit` (O2KapN) gives the
roots `β_Q`; `core_locU` (O2Gl3f) moves the target to the relation term at `D₂`, which `rel_glob` (O2Rel7) puts in `Gr`.
* **`isUnit_natCast_of_prim_map`**: `d ∣ N` is a unit in any ring receiving `k` (`k` has a primitive `N`-th root);
* **`pp_core`** (DEF): the target class at `D₁` lies in `Gr`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.defProp false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.EtMV

theorem isUnit_natCast_of_prim_map {k A : Type} [Field k] [CommRing A] (f : k →+* A) {N d : ℕ} [NeZero N] {ζ0 : k}
    (hζ0 : IsPrimitiveRoot ζ0 N) (hdN : d ∣ N) : IsUnit ((d : ℕ) : A) := by
  have hN : ((N : ℕ) : k) ≠ 0 := hζ0.neZero'.out
  obtain ⟨m, hm⟩ := hdN
  have hd : ((d : ℕ) : k) ≠ 0 := fun h => hN (by rw [hm, Nat.cast_mul, h, zero_mul])
  have h2 := (isUnit_iff_ne_zero.2 hd).map f
  rwa [map_natCast] at h2

section PPCore

end PPCore

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2PP2 =====
section

/-!
# S4-EtPBC-A, O2 PP' (O2PP2): PP' at the chart `D₁` with `G` generic (instances and `D₂` data built here)

GLOB/REL PLAN v1 stage S4 data: for `G = g₀ c₀' t` (an opaque variable with `hGdef`), the `D_G` and
`D₂ := D₁_{c₀'}` instances (`isAffine_prdG`, `isAffine_prdUo`, Km6 instances), the `D₂` fibre data (ZarCh) and `hD₂`,
`hR₂₁`, then `pp_core` (O2PP1).
* helpers: `dvd_of_Gdef`, `tdvd_of_Gdef`, `ne_zero_of_Gdef`, `hpt_of_ne_zero`, `isUnit_locF_self`, `hzU_of`,
  `hUo_of_range`, `mem_opnDg_or`, `mem_opnDg_prd'`, `nontrivial_of_fpt`;
* **`pp_G`** (DEF): the target class at `D₁` lies in `Gr`, from the S2-S3 output and `c₀'`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.defProp false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.EtMV

section Helpers

variable {k : Type} [Field k] {P : Scheme.{0}} {a : k} {Uo Uz : P.Opens}

theorem dvd_of_Gdef {g₀ c₀' G : k[X]} (hGdef : G = g₀ * c₀' * (X - C a)) : g₀ ∣ G :=
  ⟨c₀' * (X - C a), hGdef.trans (mul_assoc _ _ _)⟩

theorem tdvd_of_Gdef {g₀ c₀' G : k[X]} (hGdef : G = g₀ * c₀' * (X - C a)) : X - C a ∣ G :=
  ⟨g₀ * c₀', hGdef.trans (mul_comm _ _)⟩

end Helpers

section PPG

end PPG

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Gl1a =====
section

/-!
# S4-EtPBC-A, O2 GLOB (O2Gl1a): residue density at the special point

GLOB/REL PLAN v1, stage S2 input (`h1` of `exists_approx_crt`, O2Ap1). Over an algebraically closed `k`:
* `exists_const_add_mul`: if `B` is unramified and essentially of finite type over `k[X]` and `q` is the only maximal
  ideal containing `t = X - a`, then every `x : B` is `c₀ + t·y` with `c₀ ∈ k[X]`;
* `chart_h1`: the same for a chart `Spec B ⟶ A¹ ⟶ P` with exactly one geometric point over `c(X = a)`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtDeg

open RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtKum

universe u

section Alg

variable {k : Type u} [Field k]

theorem isMaximal_span_X_sub_C (a : k) : (Ideal.span {X - C a} : Ideal k[X]).IsMaximal :=
  ((Ideal.span_singleton_prime (X_sub_C_ne_zero a)).2 (prime_X_sub_C a)).isMaximal
    (by rw [Ne, Ideal.span_singleton_eq_bot]; exact X_sub_C_ne_zero a)

end Alg

section Chart

end Chart

end RamanujanPetersson.EtPBC.EtDeg

end

end

-- ===== S4.Def_RP_EtPBC_A_O2PP4d =====
section

/-!
# S4-EtPBC-A, O2 PP' (O2PP4d): PP' at `D` through a chart `dm : D₁ ⟶ D` (generic `D₁`)

GLOB/REL PLAN v1 stage S1 with `D₁` generic (`φ₁`, `dm`, `d₀` opaque): transfer the class to the pieces `p₁` of `W₁`
(`locCls_kapS_chart`, O2PPTd; one radical per piece by `exists_gam`), and on each piece over `p` apply `pp_term` (O2PP4c)
with the field map `Ψ` from `hpsi`; the other pieces carry `0`.
* generic: `comp_symm_cases_mem`, `exists_cases_fun`, `isDomain_locF`; chart: `ne_zero_of_eval_ne_zero`;
* **`pp_DD1`** (DEF): the target class `ε(D)∘θ⁻¹(kapS p (kumD α))` lies in `Gr`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.defProp false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

open scoped nonZeroDivisors

universe w v u

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtDeg

section Cases

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C] {X Y Z : C} {a b c : ℕ}
  (ε : Ext.{w} X Y a) (h : a + b = c) {M : Type*} [AddCommGroup M] (θ : Ext.{w} Y Z b ≃+ M)
  (Gr : AddSubgroup (Ext.{w} X Z c))

/-- A class `K χ` with `χ = x` when `Pp` and `χ = 0` otherwise lies in `Gr` if `K x` does (no `Decidable`). -/
theorem comp_symm_cases_mem (Pp : Prop) {Ch : Type*} [AddZeroClass Ch] (K : Ch →+ M) (χ x : Ch)
    (h1 : Pp → χ = x) (h0 : ¬ Pp → χ = 0) (hx : Pp → ε.comp (θ.symm (K x)) h ∈ Gr) :
    ε.comp (θ.symm (K χ)) h ∈ Gr := by
  by_cases hp : Pp
  · rw [h1 hp]
    exact hx hp
  · rw [h0 hp, map_zero, map_zero, Ext.comp_zero]
    exact Gr.zero_mem

end Cases

/-- A function equal to `x` where `Pp` holds and `0` elsewhere. -/
theorem exists_cases_fun {ι : Type*} (Pp : ι → Prop) {Ch : ι → Type*} [∀ i, Zero (Ch i)] (x : ∀ i, Ch i) :
    ∃ χ : ∀ i, Ch i, (∀ i, Pp i → χ i = x i) ∧ (∀ i, ¬ Pp i → χ i = 0) :=
  ⟨fun i => @dite _ (Pp i) (Classical.propDecidable _) (fun _ => x i) (fun _ => 0),
    fun _ hp => dif_pos hp, fun _ hp => dif_neg hp⟩

/-- `A_f` is a domain for `f ≠ 0` in a domain `A`. -/
theorem isDomain_locF {A : Type} [CommRing A] [IsDomain A] {f : A} (hf : f ≠ 0) :
    IsDomain (Localization.Away f) :=
  IsLocalization.isDomain_localization (powers_le_nonZeroDivisors_of_noZeroDivisors hf)

section ChartNZ

end ChartNZ

section PPDD1

end PPDD1

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2PP5a =====
section

/-!
# S4-EtPBC-A, O2 PP' (O2PP5a): an `IsLoc` class at `c(a)` comes from a domain chart over a fixed cofinite `U₀`

* `prdTo`, `prdMapR_prdTo`: for `D` over `U₁ ∪ {z}` and `z ∉ U₀ ⊇ U₁`, `D ×_P U₀ ⟶ D ×_P U₁` splits `prdMapR`;
* `locCls_up`: `ε(D, U₁)∘κ = ε(D, U₀)∘Λ[prdTo]∘κ`;
* **`isLoc_chart`**: an `IsLoc` class at `z = c(a)` is `ε(chEt c φ, U₀)∘κ` for a chart `φ` with `B` a domain,
  given `g₀(a) ≠ 0` and `D_{g₀} ⊆ U₀ ∪ {z}` (`isLoc_aff_map`, shrink to `D_{φ g₀}`, `locCls_opn`, `locCls_up`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtDeg

universe u

section Up

variable {P : Scheme.{u}}

/-- Ranges pass along maps of etale `P`-schemes. -/
theorem hDr_of_hom {D₁ D : P.Etale} (d : D₁ ⟶ D) {Uo : P.Opens} {z : P}
    (hDr : ∀ v : D.left, D.hom v ∈ Uo ∨ D.hom v = z) : ∀ v : D₁.left, D₁.hom v ∈ Uo ∨ D₁.hom v = z := fun v => by
  have hw : D₁.hom v = D.hom (d.left v) :=
    (congrArg (fun f : D₁.left ⟶ P => f v) (MorphismProperty.Over.w d)).symm.trans (Scheme.Hom.comp_apply _ _ _)
  rw [hw]
  exact hDr _

theorem hDr_inf {D : P.Etale} {U₁ U₂ : P.Opens} {z : P}
    (h₁ : ∀ v : D.left, D.hom v ∈ U₁ ∨ D.hom v = z) (h₂ : ∀ v : D.left, D.hom v ∈ U₂ ∨ D.hom v = z) :
    ∀ v : D.left, D.hom v ∈ U₁ ⊓ U₂ ∨ D.hom v = z := fun v => by
  rcases h₁ v with h1 | h1
  · rcases h₂ v with h2 | h2
    · exact Or.inl (TopologicalSpace.Opens.mem_inf.2 ⟨h1, h2⟩)
    · exact Or.inr h2
  · exact Or.inr h1

end Up

section Chart

end Chart

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2PP4f =====
section

/-!
# S4-EtPBC-A, O2 PP' (O2PP4f): PP' at a chart `D` for a piece `p` and a Kummer radical `α`

GLOB/REL PLAN v1 stage S1: `u = x / y` with `x ∣ c_x`, `y ∣ c_y` (`exists_frac_dvd`, (3a)), the density element `L`
(`exists_L`, (3b), algebra `gamAlg`), the splits `c_• = t^e c_•'`, `L = t^e L'` (`exists_eq_pow_mul_eval_ne_zero`, (3c)) and
`F := g₀ L' c_x' c_y'` (opaque via `∃`-elim), then `pp_D1` (O2PP4e).
* helpers: `ne_zero_of_pow_eq`, `F_facts`;
* **`pp_D`** (DEF): the target class `ε(D)∘θ⁻¹(kapS p (kumD α))` lies in `Gr`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.defProp false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian Polynomial

open scoped nonZeroDivisors

noncomputable section

namespace RamanujanPetersson.EtPBC.EtKum

open RamanujanPetersson.EtPBC RamanujanPetersson.EtPBC.EtMV RamanujanPetersson.EtPBC.EtDeg

/-- `α^d = u` with `α` a unit forces `u ≠ 0`. -/
theorem ne_zero_of_pow_eq {K L : Type*} [CommSemiring K] [Semiring L] [Nontrivial L] [Algebra K L] {α : Lˣ}
    {d : ℕ} {u : K} (hu : (α : L) ^ d = algebraMap K L u) : u ≠ 0 := by
  rintro rfl
  rw [map_zero] at hu
  exact (α ^ d).ne_zero (by rw [Units.val_pow_eq_pow_val, hu])

section PPD

end PPD

end RamanujanPetersson.EtPBC.EtKum

end

end

-- ===== S4.Def_RP_EtPBC_A_O2Mob =====
section

/-!
# S4-EtPBC-A, O2 Mob: charts of `P¹` missing one moved point at infinity

* `mobA c`: the shear `X₀ ↦ X₀ + c X₁`, `X₁ ↦ X₁`; `mobG c` the graded ring hom; `mobP c := Proj.map (mobG c)`,
  an isomorphism of `P¹` with inverse `mobP (-c)`.
* **`chartM c := chartA1 ≫ mobP c`**: an open immersion `A¹ ⟶ P¹` whose range is `P¹ ∖ {mobP c ∞}`
  (`mem_range_chartM`); `c ↦ mobP c ∞` is injective (`mobP_infPt_injective`).
-/

set_option autoImplicit false

open AlgebraicGeometry MvPolynomial CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace RamanujanPetersson.EtCompact

section Mob

variable {K : Type} [Field K]

/-- The shear `X₀ ↦ X₀ + c X₁`, `X₁ ↦ X₁`. -/
def mobA (c : K) : MvPolynomial (Fin 2) K →ₐ[K] MvPolynomial (Fin 2) K :=
  aeval ![X 0 + C c * X 1, X 1]

theorem mobA_X0 (c : K) : mobA c (X 0) = X 0 + C c * X 1 := by simp [mobA]

theorem mobA_X1 (c : K) : mobA c (X 1) = X 1 := by simp [mobA]

theorem mobA_comp (c c' : K) : (mobA c').comp (mobA c) = mobA (c + c') := by
  apply MvPolynomial.algHom_ext
  rw [Fin.forall_fin_two]
  refine ⟨?_, ?_⟩
  · rw [AlgHom.comp_apply, mobA_X0, map_add, map_mul, mobA_X0, mobA_X1, algHom_C, mobA_X0, C_add,
      MvPolynomial.algebraMap_eq]
    ring
  · rw [AlgHom.comp_apply, mobA_X1, mobA_X1, mobA_X1]

theorem mobA_zero : mobA (0 : K) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  rw [Fin.forall_fin_two]
  refine ⟨?_, ?_⟩
  · rw [mobA_X0, C_0, zero_mul, add_zero, AlgHom.id_apply]
  · rw [mobA_X1, AlgHom.id_apply]

theorem mobA_mem (c : K) {i : ℕ} {x : MvPolynomial (Fin 2) K} (hx : x ∈ homogeneousSubmodule (Fin 2) K i) :
    mobA c x ∈ homogeneousSubmodule (Fin 2) K i := by
  rw [mem_homogeneousSubmodule] at hx ⊢
  have hg : ∀ j : Fin 2, (![X 0 + C c * X 1, X 1] j : MvPolynomial (Fin 2) K).IsHomogeneous 1 := by
    rw [Fin.forall_fin_two]
    refine ⟨?_, ?_⟩
    · exact (isHomogeneous_X K 0).add (isHomogeneous_C_mul_X c 1)
    · exact isHomogeneous_X K 1
  have h := hx.aeval _ hg
  rw [one_mul] at h
  exact h

/-- The shear as a graded ring hom. -/
def mobG (c : K) : homogeneousSubmodule (Fin 2) K →+*ᵍ homogeneousSubmodule (Fin 2) K where
  toRingHom := (mobA c).toRingHom
  map_mem hx := mobA_mem c hx

theorem mobG_apply (c : K) (x : MvPolynomial (Fin 2) K) : mobG c x = mobA c x := rfl

theorem mobG_comp (c c' : K) : (mobG c').comp (mobG c) = mobG (c + c') :=
  GradedRingHom.ext fun x => by
    show mobA c' (mobA c x) = mobA (c + c') x
    rw [← AlgHom.comp_apply, mobA_comp]

theorem mobG_zero : mobG (0 : K) = GradedRingHom.id _ :=
  GradedRingHom.ext fun x => by
    show mobA 0 x = x
    rw [mobA_zero, AlgHom.id_apply]

theorem proj_map_congr {f f' : homogeneousSubmodule (Fin 2) K →+*ᵍ homogeneousSubmodule (Fin 2) K} (h : f = f')
    (hf : HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 2) K) ≤
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 2) K)).map f)
    (hf' : HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 2) K) ≤
      (HomogeneousIdeal.irrelevant (homogeneousSubmodule (Fin 2) K)).map f') :
    Proj.map f hf = Proj.map f' hf' := by
  subst h
  rfl

end Mob

end RamanujanPetersson.EtCompact

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L1a =====
section

/-!
# S4-EtPBC-A, L1a (MVr combinatorics): exactness of the free MV complex fibrewise over `C`

For maps `p₁ : A' → A`, `p₂ : A' → B`, `w : A → C`, `v : B → C` with `w ∘ p₁ = v ∘ p₂`, the complex
`Λ[A'] → Λ[A] ⊕ Λ[B] → Λ[C]`, `l ↦ (p₁ l, -p₂ l)`, `(p, q) ↦ w p + v q`, is exact (and the first map injective,
the last surjective) when every `c : C` satisfies `MVG1` (one point of `A` over `c`, `p₂` bijective over `c`) or
`MVG2` (one point of `B` over `c`, `p₁` bijective over `c`): `mv_inj`, `mv_surj`, `mv_exact`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

section MVComb

universe u₀ u₁ u₂ u₃ u₄

variable {Λ : Type u₀} [CommRing Λ] {A' : Type u₁} {A : Type u₂} {B : Type u₃} {C : Type u₄}
  (p₁ : A' → A) (p₂ : A' → B) (w : A → C) (v : B → C)

/-- MV case 1 at `c`: at most one and at least one point of `A` over `c`, and `p₂` bijective over `c`. -/
def MVG1 (c : C) : Prop :=
  (∀ a a', w a = c → w a' = c → a = a') ∧ (∃ a, w a = c) ∧ ∀ b, v b = c → ∃! a', p₂ a' = b

/-- MV case 2 at `c`: exactly one point of `B` over `c`, and `p₁` bijective over `c`. -/
def MVG2 (c : C) : Prop :=
  (∀ b b', v b = c → v b' = c → b = b') ∧ (∃ b, v b = c) ∧ ∀ a, w a = c → ∃! a', p₁ a' = a

theorem mapDomain_apply_unique {α : Type u₁} {β : Type u₂} (g : α → β) (l : α →₀ Λ) {b : β} {a₀ : α}
    (h : ∀ a, g a = b ↔ a = a₀) : Finsupp.mapDomain g l b = l a₀ := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply]
  simp only [Finsupp.single_apply, h]
  rw [Finsupp.sum, Finset.sum_ite_eq']
  split_ifs with h0
  · rfl
  · exact (Finsupp.notMem_support_iff.mp h0).symm

theorem mv_surj (hg : ∀ c, MVG1 p₂ w v c ∨ MVG2 p₁ w v c) (r : C →₀ Λ) :
    ∃ (p : A →₀ Λ) (q : B →₀ Λ), Finsupp.mapDomain w p + Finsupp.mapDomain v q = r := by
  induction r using Finsupp.induction_linear with
  | zero => exact ⟨0, 0, by simp⟩
  | add r s hr hs =>
    obtain ⟨p, q, h⟩ := hr
    obtain ⟨p', q', h'⟩ := hs
    exact ⟨p + p', q + q', by rw [Finsupp.mapDomain_add, Finsupp.mapDomain_add, ← h, ← h']; abel⟩
  | single c m =>
    rcases hg c with ⟨_, ⟨a, ha⟩, _⟩ | ⟨_, ⟨b, hb⟩, _⟩
    · exact ⟨Finsupp.single a m, 0, by rw [Finsupp.mapDomain_single, ha, Finsupp.mapDomain_zero, add_zero]⟩
    · exact ⟨0, Finsupp.single b m, by rw [Finsupp.mapDomain_single, hb, Finsupp.mapDomain_zero, zero_add]⟩

open Classical in
variable (Λ) in
/-- Correction for a point `a` of `A` (case 2 over `w a`). -/
def mvE₁ (a : A) : A' →₀ Λ :=
  if h : ¬ MVG1 p₂ w v (w a) ∧ ∃ a', p₁ a' = a then Finsupp.single (Classical.choose h.2) 1 else 0

open Classical in
variable (Λ) in
/-- Correction for a point `b` of `B` (case 1 over `v b`). -/
def mvE₂ (b : B) : A' →₀ Λ :=
  if h : MVG1 p₂ w v (v b) ∧ ∃ a', p₂ a' = b then Finsupp.single (Classical.choose h.2) (-1) else 0

open Classical in
variable (Λ) in
/-- The point of `A` over `c` in case 1. -/
def mvF (c : C) : A →₀ Λ :=
  if h : MVG1 p₂ w v c then Finsupp.single (Classical.choose h.2.1) 1 else 0

end MVComb

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2TB2b =====
section

/-!
# S4-EtPBC-A, L3b (TB2b): `tauApp2` and the KEY section identity `secMap_pull`
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtPBC

universe u

section TB2b

variable {Λ : Type u} [CommRing Λ]

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (W : Y.Etale)

theorem etHom_id_left {P : Scheme.{u}} (V : P.Etale) : (𝟙 V : V ⟶ V).left = 𝟙 V.left := rfl

omit [CommRing Λ] in
theorem chainL {A B D E F H A' : Scheme.{u}} (g1 : A ⟶ B) (i : B ⟶ D) (c : D ⟶ E) (hh : E ⟶ F) (k : F ⟶ H)
    (d : E ⟶ H) (c' : D ⟶ H) (e1 : B ⟶ A') (e' : A' ⟶ H) (p : A ⟶ A') (h1 : hh ≫ k = d) (h2 : c ≫ d = c')
    (h3 : i ≫ c' = e1 ≫ e') (h4 : g1 ≫ e1 = p) : (((g1 ≫ i) ≫ c) ≫ hh) ≫ k = p ≫ e' := by
  rw [Category.assoc, h1, Category.assoc, h2, Category.assoc, h3, ← Category.assoc, h4]

omit [CommRing Λ] in
theorem chainR {A B D G H H' : Scheme.{u}} (E : A ⟶ B) (M : B ⟶ D) (fa : D ⟶ G) (fb : G ⟶ H) (p : B ⟶ H')
    (gl : H' ⟶ G) (r : A ⟶ H') (s : H' ⟶ H) (h5 : M ≫ fa = p ≫ gl) (h6 : E ≫ p = r) (h7 : gl ≫ fb = s) :
    (E ≫ M) ≫ fa ≫ fb = r ≫ s := by
  rw [Category.assoc, ← Category.assoc M, h5, Category.assoc, h7, ← Category.assoc, h6]

end TB2b

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2TB3 =====
section

/-!
# S4-EtPBC-A, L3 (TB3): pullback of classes `pullH` and base change of `thetaM`

* `pullH Λ g n κ := u ∘ g^*κ ∘ u⁻¹ ∈ H^n(X, Λ)` for `κ ∈ H^n(Y, Λ)` and any `g : X ⟶ Y` (`u := pullUnit Λ g`);
* `secMap_id`, `diagSec_pull` (the KEY identity at `m = 𝟙`);
* **`thetaM_pull`**: `Λ[f⁻¹W] ⟶ f^*Λ[W]` followed by `f^*(thetaM m 1 κ)` equals
  `thetaM (f⁻¹ m) 1 (pullH f_W 1 κ)` followed by `Λ[f⁻¹T] ⟶ f^*Λ[T]`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact

universe u

section TB3

variable {Λ : Type u} [CommRing Λ]

theorem ext_comp_iso_cancel {C : Type*} [Category C] [Abelian C] [HasExt.{u} C] {A B B' : C} (e : B ≅ B')
    {n : ℕ} {x y : Ext.{u} A B n} (h : x.comp (Ext.mk₀ e.hom) (add_zero n) = y.comp (Ext.mk₀ e.hom) (add_zero n)) :
    x = y := by
  have h2 := congrArg (fun z => z.comp (Ext.mk₀ e.inv) (add_zero n)) h
  simpa only [Ext.comp_assoc_of_third_deg_zero, Ext.mk₀_comp_mk₀, Iso.hom_inv_id, Ext.comp_mk₀_id] using h2

section GenPL

universe w' v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

end GenPL

end TB3

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L2x =====
section

/-!
# S4-EtPBC-A, L2x (PullH extras): `pullH` along composites and along etale maps

* `mapExact_iso τ ξ`: isomorphic exact functors act alike on `Ext¹` (`τ : Φ ≅ Φ'`);
* `conjE x a b := mk₀ a ∘ x ∘ mk₀ b`, `conjE_conjE`, `mapExact_conjE`;
* `pullUnit_comp`: `Λ_X ≅ (f ≫ g)^*Λ_Z ≅ f^*g^*Λ_Z` is `Λ_X ≅ f^*Λ_Y ≅ f^*g^*Λ_Z`;
* **`pullH_comp`**: `pullH (f ≫ g) 1 κ = pullH f 1 (pullH g 1 κ)`;
* `pullUnit_res`: for etale `g`, `Λ_U ≅ g^*Λ_X ≅ res g Λ_X` is `unitRes g`;
* **`resLE_eq_pullH`**: for etale `g`, `resLE g 1 e = pullH g 1 e`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact

section IsoGen

universe w v₁ u₁ v₂ u₂

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasExt.{w} D]
  {Φ Φ' : C ⥤ D} [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
  [Φ'.Additive] [PreservesFiniteLimits Φ'] [PreservesFiniteColimits Φ']

/-- Conjugation `mk₀ a ∘ x ∘ mk₀ b` of a degree-one class. -/
def conjE {A A' B B' : C} (x : Ext.{w} A B 1) (a : A' ⟶ A) (b : B ⟶ B') : Ext.{w} A' B' 1 :=
  (Ext.mk₀ a).comp (x.comp (Ext.mk₀ b) (add_zero 1)) (zero_add 1)

theorem conjE_conjE {A A' A'' B B' B'' : C} (x : Ext.{w} A B 1) (a : A' ⟶ A) (b : B ⟶ B') (a' : A'' ⟶ A')
    (b' : B' ⟶ B'') : conjE (conjE x a b) a' b' = conjE x (a' ≫ a) (b ≫ b') := by
  unfold conjE
  rw [Ext.comp_assoc_of_third_deg_zero (Ext.mk₀ a) (x.comp (Ext.mk₀ b) (add_zero 1)) (Ext.mk₀ b') (zero_add 1),
    Ext.comp_assoc_of_third_deg_zero x (Ext.mk₀ b) (Ext.mk₀ b') (add_zero 1), Ext.mk₀_comp_mk₀,
    Ext.mk₀_comp_mk₀_assoc]

theorem mapExact_conjE {A A' B B' : C} (x : Ext.{w} A B 1) (a : A' ⟶ A) (b : B ⟶ B') :
    (conjE x a b).mapExactFunctor Φ = conjE (x.mapExactFunctor Φ) (Φ.map a) (Φ.map b) := by
  unfold conjE
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.mapExactFunctor_mk₀]

end IsoGen

universe u

section PullX

end PullX

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L5a =====
section

/-!
# S4-EtPBC-A, L5a (Geo1): the horizontal section through a closed point of `P¹_K`

`K` algebraically closed, `z` a closed point of `P¹_K`:
* `pt_factor`: a morphism `Spec Ω ⟶ X` hitting `z` factors through the `K`-point of `z` (`pointOfClosedPoint`);
* `σz : S ⟶ P¹_S`, `t ↦ (z, t)`, a section of `qV` (`σz_qV`, `σz_pr`);
* **`geom_factor`**: a morphism `x : Spec Ω ⟶ P¹_S` with `pr (x pt) = z` is `(x ≫ qV) ≫ σz`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtCompact RamanujanPetersson.EtPBC

universe u

section PtFactor

variable {X : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K] (f : X ⟶ Spec (CommRingCat.of K))
  [LocallyOfFiniteType f] (z : X) (hz : IsClosed ({z} : Set X))

/-- A morphism from the spectrum of a field hitting the closed point `z` factors through the `K`-point of `z`. -/
theorem pt_factor {Ω : Type u} [Field Ω] (h : Spec (CommRingCat.of Ω) ⟶ X)
    (hh : h (IsLocalRing.closedPoint Ω) = z) : h = (h ≫ f) ≫ pointOfClosedPoint f z hz := by
  subst hh
  have e := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField Ω X h
  calc h = Spec.map (Scheme.descResidueField (Scheme.stalkClosedPointTo h)) ≫
        X.fromSpecResidueField (h (IsLocalRing.closedPoint Ω)) := e.symm
    _ = (Spec.map (Scheme.descResidueField (Scheme.stalkClosedPointTo h)) ≫
        X.fromSpecResidueField (h (IsLocalRing.closedPoint Ω)) ≫ f) ≫
          pointOfClosedPoint f (h (IsLocalRing.closedPoint Ω)) hz := by
        rw [pointOfClosedPoint, ← SpecMap_residueFieldIsoBase_inv f _ hz, Category.assoc,
          ← Category.assoc (Spec.map (residueFieldIsoBase f _ hz).inv), ← Spec.map_comp, Iso.hom_inv_id,
          Spec.map_id, Category.id_comp]
    _ = (h ≫ f) ≫ pointOfClosedPoint f (h (IsLocalRing.closedPoint Ω)) hz := by
        rw [← Category.assoc _ _ f, e]

end PtFactor

section Sec

end Sec

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L5b =====
section

/-!
# S4-EtPBC-A, L5b (Geo2): the graph-open `D̃ ⊆ W ×_P Z` and its fibre lemma

Generic setting: `i : S ⟶ P` a closed immersion with a retraction `g` (`i ≫ g = 𝟙`), `W : P.Etale`.
* `Vs = W ×_P S` (`etPull i`), `Zs = Vs ×_S P` (`etPull g`), `Es = W ×_P Zs` (`prd`);
* `jz : Vs ⟶ Zs` (`v ↦ (v, i v)`), `τz : Vs ⟶ Es` (`v ↦ (w v, jz v)`), `δz : Vs ⟶ Es ×_P S` (an open immersion:
  an etale section of `rz`, `δz_rz`);
* `Og Q = (κ '' (range δz)ᶜ)ᶜ ∩ Es⁻¹ Q` (`κ = pullback.fst _ i`, a closed immersion), `Dg = opn Es Og`,
  `wg : Dg ⟶ Zs`;
* **`fl_graph`**: at `x̄` with `x̄ = (x̄ ≫ g) ≫ i`, a point `d` of `Es` off `κ '' (range δz)ᶜ` is `τz` of its `Zs`-part;
* **`graph_unique`**, **`graph_exists`** (`x ∈ Q`): `wg` is bijective on fibres over such `x̄`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits

noncomputable section

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtPBC

universe u

section Graph

variable {P S : Scheme.{u}} (i : S ⟶ P) (g : P ⟶ S) (W : P.Etale)

variable {i g} (hig : i ≫ g = 𝟙 S)

variable [IsClosedImmersion i]

theorem spec_pt_eq {Ω : Type u} [Field Ω] (y y' : Spec (CommRingCat.of Ω)) : y = y' := by
  have : Subsingleton (PrimeSpectrum Ω) := inferInstance
  exact Subsingleton.elim (α := PrimeSpectrum Ω) y y'

end Graph

end RamanujanPetersson.EtPBC.EtMV

end

end

-- ===== S4.Def_RP_EtPBC_A_O2L7a =====
section

/-!
# S4-EtPBC-A, O2 L7a: pullback along an isomorphism is an equivalence; germ images are subgroups
* `Delta.bcImg`: the germ image `{β | ∃ j α, bc j α = β}` is an additive subgroup (cofiltered `J`);
* `etPullId`: `etPull (𝟙 X) ≅ 𝟭`; `pushId`: `push (𝟙 X) ≅ 𝟭`; `pushEquiv e` for an isomorphism `e`;
* **`pull_isEquivalence`**: `e^*` is an equivalence for an isomorphism `e`;
* **`pull_ext_bijective`**: `e^*` is bijective on `Ext^n`.
-/

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits Opposite Abelian

noncomputable section

namespace RamanujanPetersson.EtPBC.Delta

universe w v₁ u₁ v₂ u₂ v₃ u₃

end RamanujanPetersson.EtPBC.Delta

namespace RamanujanPetersson.EtPBC.EtMV

open RamanujanPetersson.EtPBC RamanujanPetersson.EtCompact

universe u

section L7a

variable {Λ : Type u} [CommRing Λ]

theorem fst_lift_id {X : Scheme.{u}} (V : X.Etale) :
    pullback.fst V.hom (𝟙 X) ≫ pullback.lift (𝟙 V.left) V.hom (by simp) = 𝟙 _ := by
  apply pullback.hom_ext
  · exact (Category.assoc _ _ _).trans ((congrArg (fun k => pullback.fst V.hom (𝟙 X) ≫ k)
      (pullback.lift_fst _ _ _)).trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  · exact (Category.assoc _ _ _).trans ((congrArg (fun k => pullback.fst V.hom (𝟙 X) ≫ k)
      (pullback.lift_snd _ _ _)).trans ((pullback.condition.trans (Category.comp_id _)).trans
        (Category.id_comp _).symm))

end L7a

end RamanujanPetersson.EtPBC.EtMV

end

end


