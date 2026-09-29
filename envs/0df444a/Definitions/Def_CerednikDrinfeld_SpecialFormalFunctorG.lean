-- Prove2me | Definitions.Def_CerednikDrinfeld_SpecialFormalFunctorG
-- name    : CerednikDrinfeld_SpecialFormalFunctorG
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/14dad99c-5ebe-5715-9ead-6401cf5e6ddf
-- title:
--   Translation relations and Drinfeld's moduli functor G
-- statement:
--   Fix a prime $p$, a commutative ring $O$, a formal $\mathcal O_D$-module $\Phi$ over $O/pO$ in the project's sense (`FormalODModule`: a commutative two-dimensional formal group law $F$ together with an action of $\mathbb Z_{p^2}=W(\mathbb F_{p^2})$ by endomorphisms and a series $\varpi$ with $\varpi\circ\varpi=[p]$ and $\varpi\circ[a]=[\sigma a]\circ\varpi$), and a `ModuliPackage` $M$ on pairs $(B,\psi:O\to B)$ with $p$ nilpotent. `frobSeries B j` is the pair of monomials $(X_0^{p^j},X_1^{p^j})$. For rigidified objects $t=(X,n,\rho)$, $t'=(X',n',\rho')$ over $B$ (here $\rho$ is an isogeny $\bar\Phi\to\bar X$ over $B/pB$), `Rigidified.IsTranslate e k m' ψ t t'` asserts $X'=X$ on the nose together with the existence of an auxiliary exponent $c\in\mathbb N$ for which $[p^{c+n+k}]_{\bar X}\circ\rho'\circ\mathrm{Frob}^{m'}=[p^{c+n'}]_{\bar X}\circ\rho\circ e_\psi\circ\mathrm{Frob}^{2k}$, where $e_\psi$ is the base change of the series $e$ along $\psi \bmod p$; thus the relation is a denominator-free congruence between the two rigidifications rather than an isomorphism. `Rigidified.IsPiTranslate ψ t t'` asks that $X'$ have the same group law and same $\varpi$ as $X$ but $\mathbb Z_{p^2}$-action precomposed with the Witt-vector Frobenius, and that $[p^{c+n}]_{\bar X}\circ\rho'\circ\mathrm{Frob}=[p^{c+n'}]_{\bar X}\circ\rho\circ\varpi_\Phi$ for some such $c$.
--
--   `GPoint 𝒪 M B` packages an $\mathcal O$-algebra map $\psi:O\to B$, a proof that $p$ is nilpotent in $B$, and a point of $M(B,\psi)$; with functorial transport along $\mathcal O$-algebra maps (`map`, with `map_id`, `map_comp`, and the extensionality lemma `ext'`) this yields the `AlgFunctor` $G$ with $G(B)=\coprod_\psi M(B,\psi)$. `G.LocallyLifts` says that, after a Zariski cover of $B$ by finitely many $f_i$ generating the unit ideal, over every localisation $L=B[1/f_i]$ with $p$ nilpotent the two restricted points are of the form $\eta(t),\eta(t')$ for admissible rigidified objects $t,t'$ satisfying a given relation. `G.IsTranslate e k m'` combines this, with the relation `Rigidified.IsTranslate`, with the twist $\psi'=\psi\circ\mathrm{Fr}^{m'-2k}$ of structure maps; `G.IsPiTranslate` does the same with $\psi'=\psi\circ\mathrm{Fr}$ and the relation `Rigidified.IsPiTranslate`. Finally, given a ring map $E_0$ from the centralizer of the $\mathbb Z_{p^2}$-action and $\varpi$ in $\operatorname{End}\Phi$ into $2\times2$ matrices over a field $K$, `G.IsActBy E₀ g x x'` asserts the existence of $e$ in that centralizer and $k,m'\in\mathbb N$ with $E_0(e)=p^k g^{-1}$, with $e$ having kernel of degree $p^{2m'}$, and with $x'$ a translate of $x$ by $e$ in the above sense. All declarations are data or relations; nothing is asserted.
--
--   **Relation to Mathlib.** Mathlib has no formal $\mathcal O_D$-modules, rigidifications or Drinfeld moduli functors; these are the project's own notions, built on Mathlib's multivariate power series substitution, Witt vectors, `IsLocalization.Away` and algebra homomorphisms.
--
--   **Where it is used.** These relations express the action of $GL_2$ of the local field, and of the uniformiser $\Pi$ of the quaternion algebra, on Drinfeld's moduli functor, in the form needed to state its equivariant comparison with the formal upper half plane; this is the Čerednik–Drinfeld input to the study of Shimura curves used in the level-lowering part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_SpecialFormalFunctorG.lean

import Mathlib
import Definitions.Def_MvFormalGroup_NegV2
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

universe u v

namespace CerednikDrinfeld
namespace SpecialFormal

open FormalOmega

variable {p : ℕ} [Fact p.Prime]

namespace Rigidified

variable {O : Type v} [CommRing O] {Φ : FormalODModule p (O ⧸ pIdeal p O)}
variable {B : Type u} [CommRing B]

def frobSeries (B : Type u) [CommRing B] (j : ℕ) : Series B :=
  fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) B) ^ (p ^ j)

def IsTranslate (e : Series (O ⧸ pIdeal p O)) (k m' : ℕ) (ψ : O →+* B) (t t' : Rigidified p Φ B) :
    Prop :=
  t'.X = t.X ∧
    ∃ c : ℕ,
      (t.Xbar.act ((p : Zp2 p) ^ (c + t.n + k))).comp (t'.ρ.comp (frobSeries (p := p) _ m')) =
        (t.Xbar.act ((p : Zp2 p) ^ (c + t'.n))).comp
          (t.ρ.comp ((Series.map (residueMap ψ) e).comp (frobSeries (p := p) _ (2 * k))))

def IsPiTranslate (ψ : O →+* B) (t t' : Rigidified p Φ B) : Prop :=
  t'.X.F = t.X.F ∧ t'.X.varpi = t.X.varpi ∧ (∀ a, t'.X.act a = t.X.act (WittVector.frobenius a)) ∧
    ∃ c : ℕ,
      (t.Xbar.act ((p : Zp2 p) ^ (c + t.n))).comp
          (t'.ρ.comp fun i => (MvPowerSeries.X i : MvPowerSeries (Fin 2) (B ⧸ pIdeal p B)) ^ p) =
        (t.Xbar.act ((p : Zp2 p) ^ (c + t'.n))).comp (t.ρ.comp (Φ.varpi.map (residueMap ψ)))

end Rigidified

namespace ModuliPackage

variable (𝒪 : Type) [CommRing 𝒪] {O : Type} [CommRing O] [Algebra 𝒪 O]

structure GPoint (M : ModuliPackage.{0, 0} p O) (B : Type) [CommRing B] [Algebra 𝒪 B] : Type where

  ψ : O →ₐ[𝒪] B

  nilp : IsNilpotent (p : B)

  pt : M.obj B (ψ : O →+* B) nilp

namespace GPoint

variable {𝒪}
variable {M : ModuliPackage.{0, 0} p O} {B : Type} [CommRing B] [Algebra 𝒪 B]

theorem ext' {x y : GPoint 𝒪 M B} (h₁ : x.ψ = y.ψ) (h₂ : HEq x.pt y.pt) : x = y := by
  obtain ⟨ψ, n, m⟩ := x
  obtain ⟨ψ', n', m'⟩ := y
  cases h₁
  cases h₂
  rfl

def map {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (φ : B →ₐ[𝒪] B') (x : GPoint 𝒪 M B) :
    GPoint 𝒪 M B' where
  ψ := φ.comp x.ψ
  nilp := by simpa only [map_natCast] using x.nilp.map (φ : B →+* B')
  pt := M.map x.nilp (by simpa only [map_natCast] using x.nilp.map (φ : B →+* B'))
    (φ : B →+* B') rfl x.pt

@[simp] theorem map_ψ {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (φ : B →ₐ[𝒪] B') (x : GPoint 𝒪 M B) :
    (x.map φ).ψ = φ.comp x.ψ := rfl

theorem map_pt {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (φ : B →ₐ[𝒪] B') (x : GPoint 𝒪 M B) :
    (x.map φ).pt = M.map x.nilp (x.map φ).nilp (φ : B →+* B') rfl x.pt := rfl

theorem map_id (x : GPoint 𝒪 M B) : x.map (AlgHom.id 𝒪 B) = x :=
  ext' (AlgHom.id_comp _) (heq_of_eq (M.map_id x.nilp x.pt))

theorem map_comp {B₂ : Type} [CommRing B₂] [Algebra 𝒪 B₂] {B₃ : Type} [CommRing B₃] [Algebra 𝒪 B₃]
    (f : B →ₐ[𝒪] B₂) (g : B₂ →ₐ[𝒪] B₃) (x : GPoint 𝒪 M B) :
    x.map (g.comp f) = (x.map f).map g :=
  ext' (AlgHom.comp_assoc _ _ _)
    (heq_of_eq (M.map_comp x.nilp (x.map f).nilp ((x.map f).map g).nilp (g : B₂ →+* B₃) (f : B →+* B₂)
      rfl rfl x.pt))

end GPoint

def G (M : ModuliPackage.{0, 0} p O) : AlgFunctor 𝒪 where
  obj B _ _ := GPoint 𝒪 M B
  map φ x := x.map φ
  map_id x := x.map_id
  map_comp f g x := x.map_comp f g

@[simp] theorem G_obj (M : ModuliPackage.{0, 0} p O) (B : Type) [CommRing B] [Algebra 𝒪 B] :
    (G 𝒪 M).obj B = GPoint 𝒪 M B := rfl

@[simp] theorem G_map (M : ModuliPackage.{0, 0} p O) {B : Type} [CommRing B] [Algebra 𝒪 B]
    {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (φ : B →ₐ[𝒪] B') (x : GPoint 𝒪 M B) :
    (G 𝒪 M).map φ x = x.map φ := rfl

namespace G

variable {𝒪}
variable {M : ModuliPackage.{0, 0} p O} (ι : Zp2 p →+* O) (Φ : FormalODModule p (O ⧸ pIdeal p O))
  (η : ∀ (B : Type) [CommRing B] (ψ : O →+* B) (hB : IsNilpotent (p : B)), Rigidified p Φ B → M.obj B ψ hB)
  (Fr : O ≃ₐ[𝒪] O)

def LocallyLifts {B : Type} [CommRing B] (ψ ψ' : O →+* B) (hB : IsNilpotent (p : B))
    (m : M.obj B ψ hB) (m' : M.obj B ψ' hB)
    (Rel : ∀ (L : Type) [CommRing L], (O →+* L) → Rigidified p Φ L → Rigidified p Φ L → Prop) : Prop :=
  ∃ (n : ℕ) (f : Fin n → B), Ideal.span (Set.range f) = ⊤ ∧
    ∀ (i : Fin n) (L : Type) [CommRing L] [Algebra B L] [IsLocalization.Away (f i) L]
      (hL : IsNilpotent (p : L)),
      ∃ t t' : Rigidified p Φ L,
        t.IsAdmissible ι ((algebraMap B L).comp ψ) ∧ t'.IsAdmissible ι ((algebraMap B L).comp ψ') ∧
        η L ((algebraMap B L).comp ψ) hL t = M.map (ψ' := (algebraMap B L).comp ψ) hB hL (algebraMap B L) rfl m ∧
        η L ((algebraMap B L).comp ψ') hL t' = M.map (ψ' := (algebraMap B L).comp ψ') hB hL (algebraMap B L) rfl m' ∧
        Rel L ((algebraMap B L).comp ψ) t t'

def IsTranslate (e : Series (O ⧸ pIdeal p O)) (k m' : ℕ) {B : Type} [CommRing B] [Algebra 𝒪 B]
    (x x' : GPoint 𝒪 M B) : Prop :=
  x'.ψ = frobTwist O Fr ((m' : ℤ) - 2 * k) x.ψ ∧
    LocallyLifts ι Φ η (x.ψ : O →+* B) (x'.ψ : O →+* B) x.nilp x.pt x'.pt
      (fun _ _ χ t t' => Rigidified.IsTranslate e k m' χ t t')

def IsPiTranslate {B : Type} [CommRing B] [Algebra 𝒪 B] (x x' : GPoint 𝒪 M B) : Prop :=
  x'.ψ = frobTwist O Fr 1 x.ψ ∧
    LocallyLifts ι Φ η (x.ψ : O →+* B) (x'.ψ : O →+* B) x.nilp x.pt x'.pt
      (fun _ _ χ t t' => Rigidified.IsPiTranslate χ t t')

def IsActBy {K : Type} [Field K] [Algebra 𝒪 K]
    (E₀ : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd}) →+* Matrix (Fin 2) (Fin 2) K)
    {B : Type} [CommRing B] [Algebra 𝒪 B] (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (x x' : GPoint 𝒪 M B) : Prop :=
  ∃ (e : Subring.centralizer (Set.range Φ.actEnd ∪ {Φ.varpiEnd})) (k m' : ℕ),
    E₀ e = (p : K) ^ k • ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) ∧
    FormalODModule.HasKernelOfDegree (e : MvFormalGroup.End Φ.F).toPowerSeries (p ^ (2 * m')) ∧
    IsTranslate ι Φ η Fr (e : MvFormalGroup.End Φ.F).toPowerSeries k m' x x'

end G

end ModuliPackage

end SpecialFormal
end CerednikDrinfeld

end


