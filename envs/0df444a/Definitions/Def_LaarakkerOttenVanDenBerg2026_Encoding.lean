-- Prove2me | Definitions.Def_LaarakkerOttenVanDenBerg2026_Encoding
-- name    : LaarakkerOttenVanDenBerg2026_Encoding
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-07T15:41:22.31777+00:00
-- url     : https://prove2.me/theorems/1c4b1803-8f1c-4d13-b7b5-4894d640e67e
-- title:
--   Wild Endofunctors, Polynomial Functors, Size-Indexed (Co)algebras, and (Co)inductive Encodings
-- statement:
--   Formalizes Section 3 (pp. 8–12) and Appendix B (pp. 24–27) of Laarakker, Otten & van den Berg (FSCD 2026): wild endofunctors $F : U \to U$ (`WildEndofunctor`), polynomial endofunctors $P_{A, B}(X) := \Sigma a : A.\,(B(a) \to X)$ (`polyEndofunctor`), size-indexed types `SizeTy` and morphisms `SizeHom`, modal actions $\Diamond$ (`diamondMap`) and $\Box$ (`boxMap`), lifted functors $F[\Diamond -]$ and $F[\Box -]$, $F$-algebras (`FAlg`, `FAlgHom`, `IsInitialFAlg`), size-indexed $F[\Diamond -]$-algebras (`SizedFAlg`), the fixpoint initial algebra $(\mu^\Diamond F, \mathsf{in}^\Diamond)$ (`muDiamondAlg`), constant lifting $T$ (`constSizedFAlg`), weak commutation with $\exists$ (`WeaklyCommutesEx`), existential algebra lifting (`exFAlg`), the inductive carrier $\mu F := \exists i.\,(\mu^\Diamond F)\,i$ (`muCarrier`, `muAlg`), and the dual coalgebra definitions (`FCoalg`, `IsTerminalFCoalg`, `SizedFCoalg`, `nuBoxCoalg`, `constSizedFCoalg`, `WeaklyCommutesAll`, `allFCoalg`, `nuCarrier`, `nuCoalg`).
-- source:
--   Bastiaan Laarakker, Daniël Otten, and Benno van den Berg, 'Constructing (Co)inductive Types via Large Sizes', FSCD 2026 (arXiv:2602.18921), Section 3 (pp. 8–12) & Appendix B (pp. 24–27)

/-
Formalization of Section 3 and Appendix B of:
  Bastiaan Laarakker, Daniël Otten, and Benno van den Berg (FSCD 2026),
  "Constructing (Co)inductive Types via Large Sizes",
  DOI: 10.4230/LIPIcs.FSCD.2026.21 (extended version: arXiv:2602.18921v2).

This file defines:
  1. Tracked small morphisms `Hom T A B`, wild endofunctors `F : U → U`, and polynomial
     endofunctors `P_{A, B}(X) := Σ (a : A), (B(a) → X)` (Section 3.1, pp. 8–9).
  2. Size-indexed types `Size → U`, uniformly tracked size-indexed morphisms `A →^i B`
     (`SizeHom`), size-indexed endofunctors, the modal actions `◇` and `□`, and the lifted
     functors `F[◇ -]` and `F[□ -]` (Section 3.2, pp. 9–10).
  3. `F`-algebras, initial `F`-algebras, size-indexed `F[◇ -]`-algebras, the fixpoint
     carrier `μ^◇ F` and structure map `in^◇`, the constant lifting `T`, weak commutation
     with `∃` (`WeaklyCommutesEx`), the existential algebra lifting `∃`, the adjunction
     comparison maps `exAdjFwd` / `exAdjInv` (`∃ ⊣ T`), and the inductive carrier
     `μ F := ∃ i. (μ^◇ F) i` (Section 3.3, Definition 6, Lemmas 7–8, Definition 9,
     Proposition 10, Theorem 11, pp. 10–12 & Appendix B, p. 24).
  4. `F`-coalgebras, terminal `F`-coalgebras, size-indexed `F[□ -]`-coalgebras, the fixpoint
     carrier `ν^□ F` and structure map `out^□`, the constant lifting `T`, weak commutation
     with `∀` (`WeaklyCommutesAll`), the universal coalgebra lifting `∀`, the adjunction
     comparison maps `allAdjFwd` / `allAdjInv` (`T ⊣ ∀`), and the coinductive carrier
     `ν F := ∀ i. (ν^□ F) i` (Section 3.4 & Appendix B, Definition 18, Lemmas 19–20,
     Definition 21, Proposition 22, Theorem 23, pp. 24–27).
-/
import Definitions.Def_LaarakkerOttenVanDenBerg2026_TypeTheory

set_option linter.checkUnivs false

namespace LaarakkerOttenVanDenBerg2026

universe u v

/-! ## 1. Tracked Morphisms, Wild Endofunctors, and Polynomial Endofunctors (Section 3.1, pp. 8–9) -/

/-- A tracked morphism `f : A → B` between small types in `T`
(Section 3.1, p. 8 & Section 4.1, p. 13). -/
@[ext]
structure Hom (T : SizeCoreTheory.{u, v}) (A B : T.U) : Type v where
  toFun : T.El A → T.El B
  tracked : T.IsTracked toFun

instance (T : SizeCoreTheory.{u, v}) (A B : T.U) :
    CoeFun (Hom T A B) (fun _ => T.El A → T.El B) where
  coe := Hom.toFun

/-- Identity morphism on a small type `A : T.U`. -/
def homId (T : SizeCoreTheory.{u, v}) (A : T.U) : Hom T A A where
  toFun := fun a => a
  tracked := ⟨.id, fun _ _ hna => hna⟩

/-- Composition of tracked morphisms `g ∘ f`. -/
def homComp (T : SizeCoreTheory.{u, v}) {A B C : T.U}
    (g : Hom T B C) (f : Hom T A B) : Hom T A C where
  toFun := fun a => g (f a)
  tracked := by
    rcases g.tracked with ⟨cg, hcg⟩
    rcases f.tracked with ⟨cf, hcf⟩
    exact ⟨.comp cg cf, fun a n hna => hcg (f a) _ (hcf a n hna)⟩

/-- Half-adjoint equivalence between decoded small types `El A` and `El B` whose inverse is
also tracked in `T`. -/
structure IsTrackedHAEquiv (T : SizeCoreTheory.{u, v}) {A B : T.U}
    (f : T.El A → T.El B) : Type v extends IsHAEquiv f where
  inv_tracked : T.IsTracked toIsHAEquiv.inv

/-- View the inverse of an `IsTrackedHAEquiv` as a tracked morphism `Hom T B A`. -/
def IsTrackedHAEquiv.invHom {T : SizeCoreTheory.{u, v}} {A B : T.U}
    {f : T.El A → T.El B} (e : IsTrackedHAEquiv T f) : Hom T B A where
  toFun := e.inv
  tracked := e.inv_tracked

/-- A (wild) endofunctor `F : U → U` on the universe of small types (Section 3.1, Remark, p. 8):
consists of an object map `obj : U → U`, a tracked morphism action
`map : Hom T A B → Hom T (obj A) (obj B)` with uniform tracker transformation `mapTracker`
and size-recursion fixpoint trackers `algFixTracker` and `coalgFixTracker`, preserving
identities and composition up to propositional equality. -/
structure WildEndofunctor (T : SizeCoreTheory.{u, v}) : Type (max u v) where
  obj : T.U → T.U
  map : {A B : T.U} → Hom T A B → Hom T (obj A) (obj B)
  mapTracker : TrackerCode → TrackerCode
  map_realises : ∀ {A B : T.U} (f : Hom T A B) (c : TrackerCode),
    (∀ (x : T.El A) (n : ℕ), T.realises n x → T.realises (evalTracker c n) (f x)) →
    ∀ (z : T.El (obj A)) (n : ℕ), T.realises n z →
      T.realises (evalTracker (mapTracker c) n) (map f z)
  algFixTracker : TrackerCode → TrackerCode
  algFixTracker_spec : ∀ (c : TrackerCode) (n : ℕ),
    evalTracker c (evalTracker (mapTracker (algFixTracker c)) n) =
      evalTracker (algFixTracker c) n
  coalgFixTracker : TrackerCode → TrackerCode
  coalgFixTracker_spec : ∀ (c : TrackerCode) (n : ℕ),
    evalTracker (mapTracker (coalgFixTracker c)) (evalTracker c n) =
      evalTracker (coalgFixTracker c) n
  map_id : ∀ (A : T.U) (x : T.El (obj A)), map (homId T A) x = x
  map_comp : ∀ {A B C : T.U} (g : Hom T B C) (f : Hom T A B)
    (x : T.El (obj A)), map (homComp T g f) x = map g (map f x)

theorem WildEndofunctor.map_congr {T : SizeCoreTheory.{u, v}} (F : WildEndofunctor T)
    {A B : T.U} {f₁ f₂ : Hom T A B} (h : ∀ x, f₁ x = f₂ x) (z : T.El (F.obj A)) :
    F.map f₁ z = F.map f₂ z := by
  have hf : f₁ = f₂ := Hom.ext (funext h)
  rw [hf]

/-- Wild category functor laws for a mapping on objects and morphisms. -/
structure IsWildFunctor {Obj₁ : Type*} {Obj₂ : Type*}
    (Hom₁ : Obj₁ → Obj₁ → Type*) (Hom₂ : Obj₂ → Obj₂ → Type*)
    (id₁ : ∀ X, Hom₁ X X) (comp₁ : ∀ {X Y Z}, Hom₁ Y Z → Hom₁ X Y → Hom₁ X Z)
    (id₂ : ∀ X, Hom₂ X X) (comp₂ : ∀ {X Y Z}, Hom₂ Y Z → Hom₂ X Y → Hom₂ X Z)
    (F₀ : Obj₁ → Obj₂) (F₁ : ∀ {X Y}, Hom₁ X Y → Hom₂ (F₀ X) (F₀ Y)) : Prop where
  map_id : ∀ X, F₁ (id₁ X) = id₂ (F₀ X)
  map_comp : ∀ {X Y Z} (g : Hom₁ Y Z) (f : Hom₁ X Y),
    F₁ (comp₁ g f) = comp₂ (F₁ g) (F₁ f)

/-- Action of the polynomial functor `P_{A, B}` on decoded pairs `(a : El A) × El (B a →^U X)`. -/
def polyMapPair (T : SizeCoreTheory.{u, v}) (A : T.U) (B : T.El A → T.U)
    {X Y : T.U} (f : Hom T X Y)
    (p : (a : T.El A) × T.El (T.arrU (B a) X)) :
    (a : T.El A) × T.El (T.arrU (B a) Y) :=
  ⟨p.1, T.mapArr f f.tracked p.2⟩

/-- The polynomial endofunctor `P_{A, B}(X) := Σ (a : A), (B(a) → X)` associated with
a small node-shape type `A : U` and branching-arity family `B : El A → U`
(Section 3.1, pp. 8–9). -/
def polyEndofunctor (T : SizeCoreTheory.{u, v}) (A : T.U) (B : T.El A → T.U) :
    WildEndofunctor T where
  obj X := T.sigmaU A (fun a => T.arrU (B a) X)
  map {X Y} f := {
    toFun := fun z =>
      (T.El_sigmaU A (fun a => T.arrU (B a) Y)).symm
        (polyMapPair T A B f (T.El_sigmaU A (fun a => T.arrU (B a) X) z))
    tracked := by
      rcases f.tracked with ⟨cf, hcf⟩
      refine ⟨polyTracker cf, fun z n hnz => ?_⟩
      rcases (T.realises_sigmaU z n).mp hnz with ⟨hn1, hn2⟩
      exact T.realises_sigmaMk (fun a => T.arrU (B a) Y)
        (T.El_sigmaU A (fun a => T.arrU (B a) X) z).1
        (T.mapArr f f.tracked (T.El_sigmaU A (fun a => T.arrU (B a) X) z).2)
        hn1 (T.realises_mapArr f f.tracked cf hcf _ hn2)
  }
  mapTracker := polyTracker
  map_realises {X Y} f cf hcf z n hnz := by
    rcases (T.realises_sigmaU z n).mp hnz with ⟨hn1, hn2⟩
    exact T.realises_sigmaMk (fun a => T.arrU (B a) Y)
      (T.El_sigmaU A (fun a => T.arrU (B a) X) z).1
      (T.mapArr f f.tracked (T.El_sigmaU A (fun a => T.arrU (B a) X) z).2)
      hn1 (T.realises_mapArr f f.tracked cf hcf _ hn2)
  algFixTracker := .alg
  algFixTracker_spec := fun _ _ => rfl
  coalgFixTracker := .coalg
  coalgFixTracker_spec := fun _ _ => rfl
  map_id X z := by
    change (T.El_sigmaU A (fun a => T.arrU (B a) X)).symm
      (polyMapPair T A B (homId T X) (T.El_sigmaU A (fun a => T.arrU (B a) X) z)) = z
    unfold polyMapPair
    have hid : T.mapArr (homId T X).toFun (homId T X).tracked
        ((T.El_sigmaU A (fun a => T.arrU (B a) X) z).2) =
        ((T.El_sigmaU A (fun a => T.arrU (B a) X) z).2) :=
      T.mapArr_id _
    rw [hid]
    exact (T.El_sigmaU A (fun a => T.arrU (B a) X)).symm_apply_apply z
  map_comp {X Y Z} g f z := by
    change (T.El_sigmaU A (fun a => T.arrU (B a) Z)).symm
      (polyMapPair T A B (homComp T g f) (T.El_sigmaU A (fun a => T.arrU (B a) X) z)) =
      (T.El_sigmaU A (fun a => T.arrU (B a) Z)).symm
        (polyMapPair T A B g (T.El_sigmaU A (fun a => T.arrU (B a) Y)
          ((T.El_sigmaU A (fun a => T.arrU (B a) Y)).symm
            (polyMapPair T A B f (T.El_sigmaU A (fun a => T.arrU (B a) X) z)))))
    rw [Equiv.apply_symm_apply]
    unfold polyMapPair
    dsimp only
    have hcomp : T.mapArr (homComp T g f).toFun (homComp T g f).tracked
        ((T.El_sigmaU A (fun a => T.arrU (B a) X) z).2) =
        T.mapArr g.toFun g.tracked (T.mapArr f.toFun f.tracked
          ((T.El_sigmaU A (fun a => T.arrU (B a) X) z).2)) :=
      T.mapArr_comp g.toFun f.toFun _
    rw [hcomp]

/-! ## 2. Size-Indexed Types, Morphisms, and Endofunctors (Section 3.2, pp. 9–10) -/

/-- The category of size-indexed small types has objects `SizeTy T := T.Size → T.U`
(Section 3.1, p. 8). -/
abbrev SizeTy (T : SizeCoreTheory.{u, v}) : Type u := T.Size → T.U

/-- A size-indexed morphism `f : A →^i B` is a uniformly tracked family
`∀ i : Size, El (A i) → El (B i)` (Section 3.1, p. 8 & Section 4.5, p. 15). -/
@[ext]
structure SizeHom (T : SizeCoreTheory.{u, v}) (A B : SizeTy T) : Type (max u v) where
  toFun : (i : T.Size) → T.El (A i) → T.El (B i)
  tracked : ∃ (c : TrackerCode), ∀ (i : T.Size) (x : T.El (A i)) (n : ℕ),
    T.realises n x → T.realises (evalTracker c n) (toFun i x)

instance (T : SizeCoreTheory.{u, v}) (A B : SizeTy T) :
    CoeFun (SizeHom T A B) (fun _ => (i : T.Size) → T.El (A i) → T.El (B i)) where
  coe := SizeHom.toFun

/-- Component `f i : Hom T (A i) (B i)` of a size-indexed morphism `f : A →^i B` at size `i`. -/
def SizeHom.atSize {T : SizeCoreTheory.{u, v}} {A B : SizeTy T}
    (f : SizeHom T A B) (i : T.Size) : Hom T (A i) (B i) where
  toFun := f i
  tracked := by
    rcases f.tracked with ⟨c, hc⟩
    exact ⟨c, hc i⟩

/-- Identity size-indexed morphism `id : A →^i A`. -/
def sizeHomId (T : SizeCoreTheory.{u, v}) (A : SizeTy T) : SizeHom T A A where
  toFun := fun _ a => a
  tracked := ⟨.id, fun _ _ _ hna => hna⟩

/-- Composition of size-indexed morphisms `g ∘^i f : A →^i C`. -/
def sizeHomComp (T : SizeCoreTheory.{u, v}) {A B C : SizeTy T}
    (g : SizeHom T B C) (f : SizeHom T A B) : SizeHom T A C where
  toFun := fun i a => g i (f i a)
  tracked := by
    rcases g.tracked with ⟨cg, hcg⟩
    rcases f.tracked with ⟨cf, hcf⟩
    exact ⟨.comp cg cf, fun i a n hna => hcg i (f i a) _ (hcf i a n hna)⟩

/-- A size-indexed endofunctor on `Size → U` (Section 3.2, p. 9). -/
structure SizeEndofunctor (T : SizeCoreTheory.{u, v}) : Type (max u v) where
  obj : SizeTy T → SizeTy T
  map : {A B : SizeTy T} → SizeHom T A B → SizeHom T (obj A) (obj B)
  map_id : ∀ (A : SizeTy T) (i : T.Size) (x : T.El (obj A i)),
    map (sizeHomId T A) i x = x
  map_comp : ∀ {A B C : SizeTy T} (g : SizeHom T B C) (f : SizeHom T A B)
    (i : T.Size) (x : T.El (obj A i)),
    map (sizeHomComp T g f) i x = map g i (map f i x)

/-- Morphism action `◇_{A, B} f : ◇ A →^i ◇ B` of the bounded existential modality `◇`,
sending `⟨j, ⟨p, a⟩⟩^∃ ↦ ⟨j, ⟨p, f j a⟩⟩^∃` (Proposition 4, p. 9). -/
def diamondMap (T : SizeCoreTheory.{u, v}) {A B : SizeTy T}
    (f : SizeHom T A B) : SizeHom T (T.diamondU A) (T.diamondU B) where
  toFun := fun _ z =>
    T.elimDiamond (fun j p a => T.pairDiamond j p (f j a)) (by
      rcases f.tracked with ⟨cf, hcf⟩
      exact ⟨cf, fun j p a n hna => T.realises_pairDiamond j p (f j a) (hcf j a n hna)⟩) z
  tracked := by
    rcases f.tracked with ⟨cf, hcf⟩
    refine ⟨cf, fun i z n hnz => ?_⟩
    exact T.realises_elimDiamond (fun j p a => T.pairDiamond j p (f j a)) _ cf
      (fun j p a m hma => T.realises_pairDiamond j p (f j a) (hcf j a m hma)) z hnz

@[simp]
theorem diamondMap_pairDiamond (T : SizeCoreTheory.{u, v}) {A B : SizeTy T}
    (f : SizeHom T A B) (i j : T.Size) (p : T.Lt j i) (a : T.El (A j)) :
    diamondMap T f i (T.pairDiamond j p a) = T.pairDiamond j p (f j a) :=
  T.elimDiamond_beta _ _ j p a

/-- Morphism action `□_{A, B} f : □ A →^i □ B` of the bounded universal modality `□`,
sending `g ↦ λ j < i. f j (g j)` (Proposition 5, p. 9). -/
def boxMap (T : SizeCoreTheory.{u, v}) {A B : SizeTy T}
    (f : SizeHom T A B) : SizeHom T (T.boxU A) (T.boxU B) where
  toFun := fun _ g =>
    T.lamBox (fun j p => f j (T.appBox g j p)) (by
      rcases f.tracked with ⟨cf, hcf⟩
      rcases T.realised g with ⟨eg, heg⟩
      exact ⟨evalTracker cf eg, fun j p => hcf j _ eg (T.realises_appBox g j p heg)⟩)
  tracked := by
    rcases f.tracked with ⟨cf, hcf⟩
    refine ⟨cf, fun i g eg heg => ?_⟩
    exact T.realises_lamBox _ _ (fun j p => hcf j _ eg (T.realises_appBox g j p heg))

@[simp]
theorem boxMap_appBox (T : SizeCoreTheory.{u, v}) {A B : SizeTy T}
    (f : SizeHom T A B) (i : T.Size) (g : T.El (T.boxU A i)) (j : T.Size) (p : T.Lt j i) :
    T.appBox (boxMap T f i g) j p = f j (T.appBox g j p) :=
  T.appBox_lamBox _ _ j p

/-- Object action `F[◇ A] i := F (◇_i A)` of a small endofunctor `F` lifted by `◇`
(Section 3.2, p. 10). -/
abbrev liftDiamondObj (T : SizeCoreTheory.{u, v}) (F : WildEndofunctor T)
    (A : SizeTy T) : SizeTy T :=
  fun i => F.obj (T.diamondU A i)

/-- Morphism action `F[◇ f]_{A, B} i := F (◇_{A, B} f i)` (Section 3.2, p. 10). -/
def liftDiamondMap (T : SizeCoreTheory.{u, v}) (F : WildEndofunctor T)
    {A B : SizeTy T} (f : SizeHom T A B) :
    SizeHom T (liftDiamondObj T F A) (liftDiamondObj T F B) where
  toFun := fun i z => F.map ((diamondMap T f).atSize i) z
  tracked := by
    rcases f.tracked with ⟨cf, hcf⟩
    refine ⟨F.mapTracker cf, fun i z n hnz => ?_⟩
    refine F.map_realises ((diamondMap T f).atSize i) cf (fun d m hmd => ?_) z n hnz
    exact T.realises_elimDiamond (fun j p a => T.pairDiamond j p (f j a)) _ cf
      (fun j p a k hka => T.realises_pairDiamond j p (f j a) (hcf j a k hka)) d hmd

/-- Object action `F[□ A] i := F (□_i A)` of a small endofunctor `F` lifted by `□`
(Section 3.2, p. 10). -/
abbrev liftBoxObj (T : SizeCoreTheory.{u, v}) (F : WildEndofunctor T)
    (A : SizeTy T) : SizeTy T :=
  fun i => F.obj (T.boxU A i)

/-- Morphism action `F[□ f]_{A, B} i := F (□_{A, B} f i)` (Section 3.2, p. 10). -/
def liftBoxMap (T : SizeCoreTheory.{u, v}) (F : WildEndofunctor T)
    {A B : SizeTy T} (f : SizeHom T A B) :
    SizeHom T (liftBoxObj T F A) (liftBoxObj T F B) where
  toFun := fun i z => F.map ((boxMap T f).atSize i) z
  tracked := by
    rcases f.tracked with ⟨cf, hcf⟩
    refine ⟨F.mapTracker cf, fun i z n hnz => ?_⟩
    refine F.map_realises ((boxMap T f).atSize i) cf (fun g eg heg => ?_) z n hnz
    exact T.realises_lamBox _ _ (fun j p => hcf j _ eg (T.realises_appBox g j p heg))

/-! ## 3. Algebras and Inductive Types (Section 3.3, pp. 10–12 & Appendix B, p. 24) -/

/-- An `F`-algebra `(A, k_A)` consists of a small carrier `A : U` and a tracked structure map
`k_A : Hom T (F A) A` (Definition 6, p. 10). -/
structure FAlg {T : SizeCoreTheory.{u, v}} (F : WildEndofunctor T) : Type (max u v) where
  carrier : T.U
  str : Hom T (F.obj carrier) carrier

/-- A morphism of `F`-algebras `(h, s_h) : (A, k_A) → (B, k_B)` consists of a tracked map
`hom : Hom T A B` and a proof `hom ∘ k_A = k_B ∘ F hom` (Definition 6, p. 10). -/
@[ext]
structure FAlgHom {T : SizeCoreTheory.{u, v}} {F : WildEndofunctor T}
    (X Y : FAlg F) : Type v where
  hom : Hom T X.carrier Y.carrier
  comm : ∀ (z : T.El (F.obj X.carrier)), hom (X.str z) = Y.str (F.map hom z)

/-- Identity `F`-algebra morphism. -/
def fAlgHomId {T : SizeCoreTheory.{u, v}} {F : WildEndofunctor T} (X : FAlg F) :
    FAlgHom X X where
  hom := homId T X.carrier
  comm := fun z => by rw [F.map_id]; rfl

/-- Composition of `F`-algebra morphisms. -/
def fAlgHomComp {T : SizeCoreTheory.{u, v}} {F : WildEndofunctor T}
    {X Y Z : FAlg F} (g : FAlgHom Y Z) (f : FAlgHom X Y) : FAlgHom X Z where
  hom := homComp T g.hom f.hom
  comm := fun z => by
    change g.hom (f.hom (X.str z)) = Z.str (F.map (homComp T g.hom f.hom) z)
    rw [f.comm, g.comm, ← F.map_comp]

/-- An `F`-algebra `I` is initial if for every `F`-algebra `X`, the type `FAlgHom I X`
is contractible (Definition 6, p. 10). -/
def IsInitialFAlg {T : SizeCoreTheory.{u, v}} {F : WildEndofunctor T}
    (I : FAlg F) : Type (max u v) :=
  ∀ (X : FAlg F), IsContr (FAlgHom I X)

/-- A size-indexed `F`-algebra (an `F[◇ -]`-algebra) consists of `carrier : Size → U`
and `str : F[◇ carrier] →^i carrier` (Section 3.3, p. 10). -/
structure SizedFAlg (T : SizeCoreTheory.{u, v}) (F : WildEndofunctor T) : Type (max u v) where
  carrier : SizeTy T
  str : SizeHom T (liftDiamondObj T F carrier) carrier

/-- A morphism of size-indexed `F[◇ -]`-algebras `(A, k_A) → (B, k_B)` (Section 3.3, p. 10). -/
@[ext]
structure SizedFAlgHom (T : SizeCoreTheory.{u, v}) {F : WildEndofunctor T}
    (X Y : SizedFAlg T F) : Type (max u v) where
  hom : SizeHom T X.carrier Y.carrier
  comm : ∀ (i : T.Size) (z : T.El (liftDiamondObj T F X.carrier i)),
    hom i (X.str i z) = Y.str i (liftDiamondMap T F hom i z)

/-- A size-indexed `F[◇ -]`-algebra `I` is initial if for every `X : SizedFAlg T F`,
the type `SizedFAlgHom T I X` is contractible (Lemma 7, p. 10 & Appendix B, p. 24). -/
def IsInitialSizedFAlg (T : SizeCoreTheory.{u, v}) {F : WildEndofunctor T}
    (I : SizedFAlg T F) : Type (max u v) :=
  ∀ (X : SizedFAlg T F), IsContr (SizedFAlgHom T I X)

/-- The fixpoint size-indexed carrier `μ^◇ F : Size → U` defined by
`μ^◇ F i := fix (λ i. λ X. F(◇_i X)) i` (Lemma 7, p. 10 & Appendix B, p. 24). -/
def muDiamond (T : SizeCoreTheory.{u, v}) (F : WildEndofunctor T) : SizeTy T :=
  fun i => (T.fix (A := fun _ => ULift.{v} T.U)
    (fun s X => ULift.up (F.obj (T.diamondBoundedU s (fun j p => (X j p).down)))) i).down

/-- The unfolding equality `μ^◇ F i = F[◇ (μ^◇ F)] i` given by `fix_beta`
(Lemma 7, p. 10 & Appendix B, p. 24). -/
theorem muDiamond_unfold (T : SizeCoreTheory.{u, v}) (F : WildEndofunctor T) (i : T.Size) :
    muDiamond T F i = liftDiamondObj T F (muDiamond T F) i :=
  congrArg ULift.down
    (T.fix_beta (A := fun _ => ULift.{v} T.U)
      (fun s X => ULift.up (F.obj (T.diamondBoundedU s (fun j p => (X j p).down)))) i)

/-- Structure map `in^◇ : F[◇ (μ^◇ F)] →^i μ^◇ F` defined by pointwise transport along
`(muDiamond_unfold T F i).symm` (Lemma 7, p. 10 & Appendix B, p. 24). -/
def inDiamond (T : SizeCoreTheory.{u, v}) (F : WildEndofunctor T) :
    SizeHom T (liftDiamondObj T F (muDiamond T F)) (muDiamond T F) where
  toFun := fun i z => Equiv.cast (congrArg T.El (muDiamond_unfold T F i).symm) z
  tracked := ⟨.id, fun i z n hnz => (T.realises_cast (muDiamond_unfold T F i).symm z n).mpr hnz⟩

/-- Inverse map `out^◇ : μ^◇ F →^i F[◇ (μ^◇ F)]` defined by pointwise transport along
`muDiamond_unfold T F i` (Appendix B, p. 24). -/
def outDiamond (T : SizeCoreTheory.{u, v}) (F : WildEndofunctor T) :
    SizeHom T (muDiamond T F) (liftDiamondObj T F (muDiamond T F)) where
  toFun := fun i m => Equiv.cast (congrArg T.El (muDiamond_unfold T F i)) m
  tracked := ⟨.id, fun i m n hnm => (T.realises_cast (muDiamond_unfold T F i) m n).mpr hnm⟩

/-- The candidate initial size-indexed `F[◇ -]`-algebra `(μ^◇ F, in^◇)`
(Lemma 7, p. 10 & Appendix B, p. 24). -/
abbrev muDiamondAlg (T : SizeCoreTheory.{u, v}) (F : WildEndofunctor T) : SizedFAlg T F where
  carrier := muDiamond T F
  str := inDiamond T F

/-- Constant size-indexed type `T A := λ i. A : Size → U` (Lemma 8, p. 11). -/
abbrev constSizeTy (T : SizeCoreTheory.{u, v}) (A : T.U) : SizeTy T :=
  fun _ => A

/-- Extraction morphism `extract_A : ◇ (T A) →^i T A` sending `⟨j, ⟨p, a⟩⟩^∃ ↦ a`
(Lemma 8, p. 11). -/
def extractDiamond (T : SizeCoreTheory.{u, v}) (A : T.U) :
    SizeHom T (T.diamondU (constSizeTy T A)) (constSizeTy T A) where
  toFun := fun _ z => T.elimDiamond (fun _ _ a => a) ⟨.id, fun _ _ _ _ hna => hna⟩ z
  tracked := ⟨.id, fun _ z _ hnz =>
    T.realises_elimDiamond (fun _ _ a => a) _ .id (fun _ _ _ _ hna => hna) z hnz⟩

@[simp]
theorem extractDiamond_pairDiamond (T : SizeCoreTheory.{u, v}) (A : T.U)
    (i j : T.Size) (p : T.Lt j i) (a : T.El A) :
    extractDiamond T A i (T.pairDiamond (A := constSizeTy T A) j p a) = a :=
  T.elimDiamond_beta (A := constSizeTy T A) (fun _ _ a => a) _ j p a

/-- Object map of the constant-lifting functor `T : F-Alg → F[◇ -]-Alg` sending
`(A, k_A)` to `(T A, k_{T A})` where `k_{T A} i := k_A ∘ F (extract_A i)` (Lemma 8, p. 11). -/
abbrev constSizedFAlg (T : SizeCoreTheory.{u, v}) {F : WildEndofunctor T}
    (X : FAlg F) : SizedFAlg T F where
  carrier := constSizeTy T X.carrier
  str := {
    toFun := fun i z => X.str (F.map ((extractDiamond T X.carrier).atSize i) z)
    tracked := by
      rcases X.str.tracked with ⟨cX, hcX⟩
      refine ⟨.comp cX (F.mapTracker .id), fun i z n hnz => ?_⟩
      refine hcX _ _ (F.map_realises ((extractDiamond T X.carrier).atSize i) .id
        (fun d m hmd => ?_) z n hnz)
      exact T.realises_elimDiamond (fun _ _ a => a) _ .id (fun _ _ _ _ hna => hna) d hmd
  }

/-- Action of `T` on a tracked map `f : Hom T A B`: `(T f) i := f` (Lemma 8, p. 11). -/
def constSizeHom (T : SizeCoreTheory.{u, v}) {A B : T.U}
    (f : Hom T A B) : SizeHom T (constSizeTy T A) (constSizeTy T B) where
  toFun := fun _ a => f a
  tracked := by
    rcases f.tracked with ⟨cf, hcf⟩
    exact ⟨cf, fun _ a n hna => hcf a n hna⟩

/-- Auxiliary map `φ_A : ∀ i, Hom T (◇_i A) (∃ j. A j)` sending `⟨j, ⟨p, a⟩⟩^∃ ↦ ⟨j, a⟩^∃`
(Definition 9, p. 11). -/
def phiEx (T : SizeCoreTheory.{u, v}) (A : SizeTy T) (i : T.Size) :
    Hom T (T.diamondU A i) (T.exU A) where
  toFun := T.elimDiamond (fun j _ a => T.pairEx j a)
    ⟨.id, fun j _ a _ hna => T.realises_pairEx j a _ hna⟩
  tracked := ⟨.id, fun z _ hnz =>
    T.realises_elimDiamond (fun j _ a => T.pairEx j a) _ .id
      (fun j _ a _ hna => T.realises_pairEx j a _ hna) z hnz⟩

@[simp]
theorem phiEx_pairDiamond (T : SizeCoreTheory.{u, v}) (A : SizeTy T)
    (i j : T.Size) (p : T.Lt j i) (a : T.El (A j)) :
    phiEx T A i (T.pairDiamond j p a) = T.pairEx j a :=
  T.elimDiamond_beta _ _ j p a

/-- Canonical comparison map `can_A : Hom T (∃ i. F[◇ A] i) (F (∃ i. A i))` defined by
`⟨i, a'⟩^∃ ↦ F (φ_A i) a'` (Definition 9, p. 11). -/
def canExF (T : SizeCoreTheory.{u, v}) (F : WildEndofunctor T) (A : SizeTy T) :
    Hom T (T.exU (liftDiamondObj T F A)) (F.obj (T.exU A)) where
  toFun := T.elimEx (fun i a' => F.map (phiEx T A i) a') (by
    refine ⟨F.mapTracker .id, fun i a' n hna' => ?_⟩
    exact F.map_realises (phiEx T A i) .id
      (fun z m hmz => T.realises_elimDiamond (fun j _ a => T.pairEx j a) _ .id
        (fun j _ a _ hna => T.realises_pairEx j a _ hna) z hmz) a' n hna')
  tracked := by
    refine ⟨F.mapTracker .id, fun w n hnw => ?_⟩
    refine T.realises_elimEx (fun i a' => F.map (phiEx T A i) a') (F.mapTracker .id)
      (fun i a' m hma' => ?_) w hnw
    exact F.map_realises (phiEx T A i) .id
      (fun z k hkz => T.realises_elimDiamond (fun j _ a => T.pairEx j a) _ .id
        (fun j _ a _ hna => T.realises_pairEx j a _ hna) z hkz) a' m hma'

@[simp]
theorem canExF_pairEx (T : SizeCoreTheory.{u, v}) (F : WildEndofunctor T)
    (A : SizeTy T) (i : T.Size) (a' : T.El (liftDiamondObj T F A i)) :
    canExF T F A (T.pairEx i a') = F.map (phiEx T A i) a' :=
  T.elimEx_beta _ _ i a'

/-- An endofunctor `F : U → U` weakly commutes with `∃` if `canExF T F A` is a tracked
half-adjoint equivalence for every `A : Size → U` (Definition 9, p. 11). -/
def WeaklyCommutesEx (T : SizeCoreTheory.{u, v}) (F : WildEndofunctor T) : Type (max u v) :=
  ∀ (A : SizeTy T), IsTrackedHAEquiv T (canExF T F A)

/-- Action `∃ f : Hom T (∃ i. A i) (∃ i. B i)` of `∃` on a size-indexed morphism
`f : A →^i B`, sending `⟨i, a⟩^∃ ↦ ⟨i, f i a⟩^∃` (Proposition 10, p. 11). -/
def exMap (T : SizeCoreTheory.{u, v}) {A B : SizeTy T} (f : SizeHom T A B) :
    Hom T (T.exU A) (T.exU B) where
  toFun := T.elimEx (fun i a => T.pairEx i (f i a)) (by
    rcases f.tracked with ⟨cf, hcf⟩
    exact ⟨cf, fun i a n hna => T.realises_pairEx i (f i a) _ (hcf i a n hna)⟩)
  tracked := by
    rcases f.tracked with ⟨cf, hcf⟩
    refine ⟨cf, fun z n hnz => ?_⟩
    exact T.realises_elimEx (fun i a => T.pairEx i (f i a)) cf
      (fun i a m hma => T.realises_pairEx i (f i a) _ (hcf i a m hma)) z hnz

@[simp]
theorem exMap_pairEx (T : SizeCoreTheory.{u, v}) {A B : SizeTy T}
    (f : SizeHom T A B) (i : T.Size) (a : T.El (A i)) :
    exMap T f (T.pairEx i a) = T.pairEx i (f i a) :=
  T.elimEx_beta _ _ i a

/-- Object map of the existential functor `∃ : F[◇ -]-Alg → F-Alg` sending `(A, k_A)` to
`(∃ i. A i, (∃ k_A) ∘ can_A⁻¹)` for `F` weakly commuting with `∃` (Proposition 10, p. 11). -/
abbrev exFAlg (T : SizeCoreTheory.{u, v}) {F : WildEndofunctor T}
    (hF : WeaklyCommutesEx T F) (X : SizedFAlg T F) : FAlg F where
  carrier := T.exU X.carrier
  str := homComp T (exMap T X.str) (hF X.carrier).invHom

/-- Underlying carrier adjunction map `Hom T (∃ i. A i) B → SizeHom T A (T B)`
(Proposition 10, p. 11). -/
def exHomToSizeHom (T : SizeCoreTheory.{u, v}) {A : SizeTy T} {B : T.U}
    (f : Hom T (T.exU A) B) : SizeHom T A (constSizeTy T B) where
  toFun := fun i a => f (T.pairEx i a)
  tracked := by
    rcases f.tracked with ⟨cf, hcf⟩
    exact ⟨cf, fun i a n hna => hcf (T.pairEx i a) n (T.realises_pairEx i a n hna)⟩

/-- Inverse carrier adjunction map `SizeHom T A (T B) → Hom T (∃ i. A i) B`
(Proposition 10, p. 11). -/
def sizeHomToExHom (T : SizeCoreTheory.{u, v}) {A : SizeTy T} {B : T.U}
    (g : SizeHom T A (constSizeTy T B)) : Hom T (T.exU A) B where
  toFun := T.elimEx g g.tracked
  tracked := by
    rcases g.tracked with ⟨cg, hcg⟩
    exact ⟨cg, fun z n hnz => T.realises_elimEx g cg hcg z hnz⟩

@[simp]
theorem sizeHomToExHom_pairEx (T : SizeCoreTheory.{u, v}) {A : SizeTy T} {B : T.U}
    (g : SizeHom T A (constSizeTy T B)) (i : T.Size) (a : T.El (A i)) :
    sizeHomToExHom T g (T.pairEx i a) = g i a :=
  T.elimEx_beta _ _ i a

/-- The full inductive carrier `μ F := ∃ i. (μ^◇ F) i : U` (Theorem 11, p. 12). -/
abbrev muCarrier (T : SizeCoreTheory.{u, v}) (F : WildEndofunctor T) : T.U :=
  T.exU (muDiamond T F)

/-- The candidate initial `F`-algebra `(μ F, in)` obtained by applying `exFAlg` to
`(μ^◇ F, in^◇)` for `F` weakly commuting with `∃` (Theorem 11, p. 12). -/
abbrev muAlg (T : SizeCoreTheory.{u, v}) {F : WildEndofunctor T}
    (hF : WeaklyCommutesEx T F) : FAlg F :=
  exFAlg T hF (muDiamondAlg T F)

/-! ## 4. Coalgebras and Coinductive Types (Section 3.4 & Appendix B, pp. 24–27) -/

/-- An `F`-coalgebra `(C, k_C)` consists of a small carrier `C : U` and a tracked structure map
`k_C : Hom T C (F C)` (Definition 18, p. 24). -/
structure FCoalg {T : SizeCoreTheory.{u, v}} (F : WildEndofunctor T) : Type (max u v) where
  carrier : T.U
  str : Hom T carrier (F.obj carrier)

/-- A morphism of `F`-coalgebras `(h, s_h) : (C, k_C) → (D, k_D)` consists of a tracked map
`hom : Hom T C D` and a proof `k_D ∘ hom = F hom ∘ k_C` (Definition 18, p. 24). -/
@[ext]
structure FCoalgHom {T : SizeCoreTheory.{u, v}} {F : WildEndofunctor T}
    (X Y : FCoalg F) : Type v where
  hom : Hom T X.carrier Y.carrier
  comm : ∀ (c : T.El X.carrier), Y.str (hom c) = F.map hom (X.str c)

/-- Identity `F`-coalgebra morphism. -/
def fCoalgHomId {T : SizeCoreTheory.{u, v}} {F : WildEndofunctor T} (X : FCoalg F) :
    FCoalgHom X X where
  hom := homId T X.carrier
  comm := fun c => by rw [F.map_id]; rfl

/-- Composition of `F`-coalgebra morphisms. -/
def fCoalgHomComp {T : SizeCoreTheory.{u, v}} {F : WildEndofunctor T}
    {X Y Z : FCoalg F} (g : FCoalgHom Y Z) (f : FCoalgHom X Y) : FCoalgHom X Z where
  hom := homComp T g.hom f.hom
  comm := fun c => by
    change Z.str (g.hom (f.hom c)) = F.map (homComp T g.hom f.hom) (X.str c)
    rw [g.comm, f.comm, ← F.map_comp]

/-- An `F`-coalgebra `N` is terminal if for every `F`-coalgebra `X`, the type `FCoalgHom X N`
is contractible (Definition 18, p. 24). -/
def IsTerminalFCoalg {T : SizeCoreTheory.{u, v}} {F : WildEndofunctor T}
    (N : FCoalg F) : Type (max u v) :=
  ∀ (X : FCoalg F), IsContr (FCoalgHom X N)

/-- A size-indexed `F`-coalgebra (an `F[□ -]`-coalgebra) consists of `carrier : Size → U`
and `str : carrier →^i F[□ carrier]` (Appendix B, p. 24). -/
structure SizedFCoalg (T : SizeCoreTheory.{u, v}) (F : WildEndofunctor T) : Type (max u v) where
  carrier : SizeTy T
  str : SizeHom T carrier (liftBoxObj T F carrier)

/-- A morphism of size-indexed `F[□ -]`-coalgebras `(C, k_C) → (D, k_D)` (Appendix B, p. 24). -/
@[ext]
structure SizedFCoalgHom (T : SizeCoreTheory.{u, v}) {F : WildEndofunctor T}
    (X Y : SizedFCoalg T F) : Type (max u v) where
  hom : SizeHom T X.carrier Y.carrier
  comm : ∀ (i : T.Size) (c : T.El (X.carrier i)),
    Y.str i (hom i c) = liftBoxMap T F hom i (X.str i c)

/-- A size-indexed `F[□ -]`-coalgebra `N` is terminal if for every `X : SizedFCoalg T F`,
the type `SizedFCoalgHom T X N` is contractible (Lemma 19, p. 25). -/
def IsTerminalSizedFCoalg (T : SizeCoreTheory.{u, v}) {F : WildEndofunctor T}
    (N : SizedFCoalg T F) : Type (max u v) :=
  ∀ (X : SizedFCoalg T F), IsContr (SizedFCoalgHom T X N)

/-- The fixpoint size-indexed carrier `ν^□ F : Size → U` defined by
`ν^□ F i := fix (λ i. λ X. F(□_i X)) i` (Lemma 19, p. 25). -/
def nuBox (T : SizeCoreTheory.{u, v}) (F : WildEndofunctor T) : SizeTy T :=
  fun i => (T.fix (A := fun _ => ULift.{v} T.U)
    (fun s X => ULift.up (F.obj (T.boxBoundedU s (fun j p => (X j p).down)))) i).down

/-- The unfolding equality `ν^□ F i = F[□ (ν^□ F)] i` given by `fix_beta`
(Lemma 19, p. 25). -/
theorem nuBox_unfold (T : SizeCoreTheory.{u, v}) (F : WildEndofunctor T) (i : T.Size) :
    nuBox T F i = liftBoxObj T F (nuBox T F) i :=
  congrArg ULift.down
    (T.fix_beta (A := fun _ => ULift.{v} T.U)
      (fun s X => ULift.up (F.obj (T.boxBoundedU s (fun j p => (X j p).down)))) i)

/-- Structure map `out^□ : ν^□ F →^i F[□ (ν^□ F)]` defined by pointwise transport along
`nuBox_unfold T F i` (Lemma 19, p. 25). -/
def outBox (T : SizeCoreTheory.{u, v}) (F : WildEndofunctor T) :
    SizeHom T (nuBox T F) (liftBoxObj T F (nuBox T F)) where
  toFun := fun i c => Equiv.cast (congrArg T.El (nuBox_unfold T F i)) c
  tracked := ⟨.id, fun i c n hnc => (T.realises_cast (nuBox_unfold T F i) c n).mpr hnc⟩

/-- Inverse map `in^□ : F[□ (ν^□ F)] →^i ν^□ F` defined by pointwise transport along
`(nuBox_unfold T F i).symm` (Appendix B, p. 25). -/
def inBox (T : SizeCoreTheory.{u, v}) (F : WildEndofunctor T) :
    SizeHom T (liftBoxObj T F (nuBox T F)) (nuBox T F) where
  toFun := fun i z => Equiv.cast (congrArg T.El (nuBox_unfold T F i).symm) z
  tracked := ⟨.id, fun i z n hnz => (T.realises_cast (nuBox_unfold T F i).symm z n).mpr hnz⟩

/-- The candidate terminal size-indexed `F[□ -]`-coalgebra `(ν^□ F, out^□)`
(Lemma 19, p. 25). -/
abbrev nuBoxCoalg (T : SizeCoreTheory.{u, v}) (F : WildEndofunctor T) : SizedFCoalg T F where
  carrier := nuBox T F
  str := outBox T F

/-- Insertion morphism `insert_C : T C →^i □ (T C)` sending `c ↦ λ j < i. c`
(Lemma 20, p. 25). -/
def insertBox (T : SizeCoreTheory.{u, v}) (C : T.U) :
    SizeHom T (constSizeTy T C) (T.boxU (constSizeTy T C)) where
  toFun := fun _ c => T.lamBox (fun _ _ => c) (by
    rcases T.realised c with ⟨n, hnc⟩
    exact ⟨n, fun _ _ => hnc⟩)
  tracked := ⟨.id, fun _ c _ hnc => T.realises_lamBox _ _ (fun _ _ => hnc)⟩

@[simp]
theorem insertBox_appBox (T : SizeCoreTheory.{u, v}) (C : T.U)
    (i : T.Size) (c : T.El C) (j : T.Size) (p : T.Lt j i) :
    T.appBox (insertBox T C i c) j p = c :=
  T.appBox_lamBox (A := constSizeTy T C) _ _ j p

/-- Object map of the constant-lifting functor `T : F-Coalg → F[□ -]-CoAlg` sending
`(C, k_C)` to `(T C, k_{T C})` where `k_{T C} i := F (insert_C i) ∘ k_C` (Lemma 20, p. 25). -/
abbrev constSizedFCoalg (T : SizeCoreTheory.{u, v}) {F : WildEndofunctor T}
    (X : FCoalg F) : SizedFCoalg T F where
  carrier := constSizeTy T X.carrier
  str := {
    toFun := fun i c => F.map ((insertBox T X.carrier).atSize i) (X.str c)
    tracked := by
      rcases X.str.tracked with ⟨cX, hcX⟩
      refine ⟨.comp (F.mapTracker .id) cX, fun i c n hnc => ?_⟩
      refine F.map_realises ((insertBox T X.carrier).atSize i) .id
        (fun x m hmx => ?_) (X.str c) (evalTracker cX n) (hcX c n hnc)
      exact T.realises_lamBox _ _ (fun _ _ => hmx)
  }

/-- Auxiliary map `ψ_C : ∀ i, Hom T (∀ j. C j) (□_i C)` sending `c' ↦ λ j < i. c' j`
(Definition 21, p. 25). -/
def psiAll (T : SizeCoreTheory.{u, v}) (C : SizeTy T) (i : T.Size) :
    Hom T (T.allU C) (T.boxU C i) where
  toFun := fun c' => T.lamBox (fun j _ => T.appAll c' j) (by
    rcases T.realised c' with ⟨n, hnc'⟩
    exact ⟨n, fun j _ => (T.realises_allU c' n).mp hnc' j⟩)
  tracked := ⟨.id, fun c' n hnc' =>
    T.realises_lamBox _ _ (fun j _ => (T.realises_allU c' n).mp hnc' j)⟩

@[simp]
theorem psiAll_appBox (T : SizeCoreTheory.{u, v}) (C : SizeTy T)
    (i : T.Size) (c' : T.El (T.allU C)) (j : T.Size) (p : T.Lt j i) :
    T.appBox (psiAll T C i c') j p = T.appAll c' j :=
  T.appBox_lamBox _ _ j p

/-- Canonical comparison map `can_C : Hom T (F (∀ i. C i)) (∀ i. F[□ C] i)` defined by
`c' ↦ λ^∀ i. F (ψ_C i) c'` (Definition 21, p. 25). -/
def canAllF (T : SizeCoreTheory.{u, v}) (F : WildEndofunctor T) (C : SizeTy T) :
    Hom T (F.obj (T.allU C)) (T.allU (liftBoxObj T F C)) where
  toFun := fun c' => T.lamAll (fun i => F.map (psiAll T C i) c') (by
    rcases T.realised c' with ⟨n, hnc'⟩
    refine ⟨evalTracker (F.mapTracker .id) n, fun i => ?_⟩
    exact F.map_realises (psiAll T C i) .id
      (fun g m hmg => T.realises_lamBox _ _ (fun j _ => (T.realises_allU g m).mp hmg j)) c' n hnc')
  tracked := by
    refine ⟨F.mapTracker .id, fun c' n hnc' => ?_⟩
    refine T.realises_lamAll _ _ (fun i => ?_)
    exact F.map_realises (psiAll T C i) .id
      (fun g m hmg => T.realises_lamBox _ _ (fun j _ => (T.realises_allU g m).mp hmg j)) c' n hnc'

@[simp]
theorem canAllF_appAll (T : SizeCoreTheory.{u, v}) (F : WildEndofunctor T)
    (C : SizeTy T) (c' : T.El (F.obj (T.allU C))) (i : T.Size) :
    T.appAll (canAllF T F C c') i = F.map (psiAll T C i) c' :=
  T.all_beta _ _ i

/-- An endofunctor `F : U → U` weakly commutes with `∀` if `canAllF T F C` is a tracked
half-adjoint equivalence for every `C : Size → U` (Definition 21, p. 25). -/
def WeaklyCommutesAll (T : SizeCoreTheory.{u, v}) (F : WildEndofunctor T) : Type (max u v) :=
  ∀ (C : SizeTy T), IsTrackedHAEquiv T (canAllF T F C)

/-- Action `∀ f : Hom T (∀ i. C i) (∀ i. D i)` of `∀` on a size-indexed morphism
`f : C →^i D`, sending `g ↦ λ^∀ i. f i (g i)` (Proposition 22, p. 26). -/
def allMap (T : SizeCoreTheory.{u, v}) {C D : SizeTy T} (f : SizeHom T C D) :
    Hom T (T.allU C) (T.allU D) where
  toFun := fun g => T.lamAll (fun i => f i (T.appAll g i)) (by
    rcases f.tracked with ⟨cf, hcf⟩
    rcases T.realised g with ⟨ng, hng⟩
    exact ⟨evalTracker cf ng, fun i => hcf i _ ng ((T.realises_allU g ng).mp hng i)⟩)
  tracked := by
    rcases f.tracked with ⟨cf, hcf⟩
    refine ⟨cf, fun g ng hng => ?_⟩
    exact T.realises_lamAll _ _ (fun i => hcf i _ ng ((T.realises_allU g ng).mp hng i))

@[simp]
theorem allMap_appAll (T : SizeCoreTheory.{u, v}) {C D : SizeTy T}
    (f : SizeHom T C D) (g : T.El (T.allU C)) (i : T.Size) :
    T.appAll (allMap T f g) i = f i (T.appAll g i) :=
  T.all_beta _ _ i

/-- Object map of the universal functor `∀ : F[□ -]-CoAlg → F-Coalg` sending `(C, k_C)` to
`(∀ i. C i, can_C⁻¹ ∘ (∀ k_C))` for `F` weakly commuting with `∀` (Proposition 22, p. 26). -/
abbrev allFCoalg (T : SizeCoreTheory.{u, v}) {F : WildEndofunctor T}
    (hF : WeaklyCommutesAll T F) (X : SizedFCoalg T F) : FCoalg F where
  carrier := T.allU X.carrier
  str := homComp T (hF X.carrier).invHom (allMap T X.str)

/-- Underlying carrier adjunction map `Hom T C (∀ i. D i) → SizeHom T (T C) D`
(Proposition 22, p. 26). -/
def allHomToSizeHom (T : SizeCoreTheory.{u, v}) {C : T.U} {D : SizeTy T}
    (f : Hom T C (T.allU D)) : SizeHom T (constSizeTy T C) D where
  toFun := fun i c => T.appAll (f c) i
  tracked := by
    rcases f.tracked with ⟨cf, hcf⟩
    exact ⟨cf, fun i c n hnc => (T.realises_allU (f c) _).mp (hcf c n hnc) i⟩

/-- Inverse carrier adjunction map `SizeHom T (T C) D → Hom T C (∀ i. D i)`
(Proposition 22, p. 26). -/
def sizeHomToAllHom (T : SizeCoreTheory.{u, v}) {C : T.U} {D : SizeTy T}
    (g : SizeHom T (constSizeTy T C) D) : Hom T C (T.allU D) where
  toFun := fun c => T.lamAll (fun i => g i c) (by
    rcases g.tracked with ⟨cg, hcg⟩
    rcases T.realised c with ⟨n, hnc⟩
    exact ⟨evalTracker cg n, fun i => hcg i c n hnc⟩)
  tracked := by
    rcases g.tracked with ⟨cg, hcg⟩
    refine ⟨cg, fun c n hnc => ?_⟩
    exact T.realises_lamAll _ _ (fun i => hcg i c n hnc)

@[simp]
theorem sizeHomToAllHom_appAll (T : SizeCoreTheory.{u, v}) {C : T.U} {D : SizeTy T}
    (g : SizeHom T (constSizeTy T C) D) (c : T.El C) (i : T.Size) :
    T.appAll (sizeHomToAllHom T g c) i = g i c :=
  T.all_beta _ _ i

/-- The full coinductive carrier `ν F := ∀ i. (ν^□ F) i : U` (Theorem 23, p. 26). -/
abbrev nuCarrier (T : SizeCoreTheory.{u, v}) (F : WildEndofunctor T) : T.U :=
  T.allU (nuBox T F)

/-- The candidate terminal `F`-coalgebra `(ν F, out)` obtained by applying `allFCoalg` to
`(ν^□ F, out^□)` for `F` weakly commuting with `∀` (Theorem 23, p. 26). -/
abbrev nuCoalg (T : SizeCoreTheory.{u, v}) {F : WildEndofunctor T}
    (hF : WeaklyCommutesAll T F) : FCoalg F :=
  allFCoalg T hF (nuBoxCoalg T F)

end LaarakkerOttenVanDenBerg2026


