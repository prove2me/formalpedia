-- Prove2me | Definitions.Def_CerednikDrinfeld_ModuliPackageDeformation
-- name    : CerednikDrinfeld_ModuliPackageDeformation
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.503845+00:00
-- url     : https://prove2.me/theorems/d97d70de-b10f-51b0-b94d-a21e7720f486
-- title:
--   Fibres, pullback rings, FP-exactness and lifting for moduli packages
-- statement:
--   Throughout, $p$ is a prime, $O$ a commutative ring, and $F$, $G$, $H$ are moduli packages over $O$ in the project's sense: assignments $B \mapsto F(B,\psi)$ of a set to each commutative ring $B$ with a ring map $\psi\colon O \to B$ and a witness that $p$ is nilpotent in $B$, together with transition maps along structure-compatible ring homomorphisms satisfying identity and composition laws; `Hom` is a morphism of such packages, given by maps $\xi_B$ commuting with all transition maps.
--
--   Four constructions are made. First, `fibre`: for $g\colon C \to B$ with $g \circ \psi_C = \psi_B$ and $x \in F(B,\psi_B)$, the subset of $F(C,\psi_C)$ of elements whose image under the transition map along $g$ is $x$. Second, for $\varphi'\colon B' \to B$ and $\varphi''\colon B'' \to B$, the ring $B' \times_B B''$ is realised as the subring `pullbackRing` of $B' \times B''$ cut out by $\varphi'(b') = \varphi''(b'')$, with the two projections `pullbackFst`, `pullbackSnd` and, given $\varphi' \circ \psi' = \varphi'' \circ \psi''$, the structure map `pullbackStr` sending $o$ to $(\psi' o, \psi'' o)$; two small lemmas record that composing `pullbackStr` with either projection returns $\psi'$, respectively $\psi''$.
--
--   Third, `IsFPExact F` asserts: whenever $\varphi'$, $\varphi''$ are surjective, compatible with the structure maps, have nilpotent kernel ideals, and $p$ is nilpotent in $B$, $B'$, $B''$ and in the pullback ring, every pair $x' \in F(B')$, $x'' \in F(B'')$ with equal images in $F(B)$ comes from a unique element of $F(B' \times_B B'')$; that is, $F(B' \times_B B'') \to F(B') \times_{F(B)} F(B'')$ is bijective, phrased as a unique-existence statement for the two projection conditions.
--
--   Fourth, `LiftsAlong ξ` asserts, for $\varphi\colon B' \to B$ surjective with $(\ker \varphi)^2 = 0$ and $x \in G(B)$: if the fibre of $H$ over $\xi_B(x)$ along $\varphi$ is non-empty, then so is the fibre of $G$ over $x$. Only non-emptiness is transferred; no compatibility between the two lifts is required.
--
--   **Relation to Mathlib.** The pullback of rings is built here as the `RingHom.eqLocus` subring of a product rather than via Mathlib's limit machinery; `fibre`, `IsFPExact` and `LiftsAlong` are conditions on the project's own `ModuliPackage` notion and have no Mathlib counterpart.
--
--   **Where it is used.** These are the functorial conditions used in the study of Drinfeld's moduli problem for special formal $\mathcal{O}$-modules: exactness for fibre products of rings with nilpotent-kernel surjections, together with lifting along square-zero extensions, is what allows statements proved for rings killed by $p$ to be propagated to all rings in which $p$ is nilpotent. The resulting Čerednik–Drinfeld uniformisation underlies the Shimura-curve inputs to the level-lowering part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_ModuliPackageDeformation.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_ModuliPackageDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace CerednikDrinfeld

namespace SpecialFormal

namespace ModuliPackage

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O]

def fibre (F : ModuliPackage.{0, 0} p O) {B C : Type} [CommRing B] [CommRing C]
    {ψB : O →+* B} {ψC : O →+* C} (hC : IsNilpotent (p : C)) (hB : IsNilpotent (p : B))
    (g : C →+* B) (hg : g.comp ψC = ψB) (x : F.obj B ψB hB) : Set (F.obj C ψC hC) :=
  {x' | F.map hC hB g hg x' = x}

def pullbackRing {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B) : Subring (B' × B'') :=
  RingHom.eqLocus (φ'.comp (RingHom.fst B' B'')) (φ''.comp (RingHom.snd B' B''))

def pullbackStr {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B) (ψ' : O →+* B') (ψ'' : O →+* B'')
    (h : φ'.comp ψ' = φ''.comp ψ'') : O →+* pullbackRing φ' φ'' :=
  (RingHom.prod ψ' ψ'').codRestrict (pullbackRing φ' φ'') (fun o => by
    show φ' (ψ' o) = φ'' (ψ'' o)
    exact congrArg (fun f : O →+* B => f o) h)

def pullbackFst {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B) : pullbackRing φ' φ'' →+* B' :=
  (RingHom.fst B' B'').comp (pullbackRing φ' φ'').subtype

def pullbackSnd {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B) : pullbackRing φ' φ'' →+* B'' :=
  (RingHom.snd B' B'').comp (pullbackRing φ' φ'').subtype

theorem pullbackFst_comp_pullbackStr {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B) (ψ' : O →+* B') (ψ'' : O →+* B'')
    (h : φ'.comp ψ' = φ''.comp ψ'') : (pullbackFst φ' φ'').comp (pullbackStr φ' φ'' ψ' ψ'' h) = ψ' :=
  RingHom.ext fun _ => rfl

theorem pullbackSnd_comp_pullbackStr {B B' B'' : Type} [CommRing B] [CommRing B'] [CommRing B'']
    (φ' : B' →+* B) (φ'' : B'' →+* B) (ψ' : O →+* B') (ψ'' : O →+* B'')
    (h : φ'.comp ψ' = φ''.comp ψ'') : (pullbackSnd φ' φ'').comp (pullbackStr φ' φ'' ψ' ψ'' h) = ψ'' :=
  RingHom.ext fun _ => rfl

def IsFPExact (F : ModuliPackage.{0, 0} p O) : Prop :=
  ∀ (B B' B'' : Type) [CommRing B] [CommRing B'] [CommRing B'']
    (ψ : O →+* B) (ψ' : O →+* B') (ψ'' : O →+* B'')
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B')) (hB'' : IsNilpotent (p : B''))
    (φ' : B' →+* B) (φ'' : B'' →+* B) (hφ' : φ'.comp ψ' = ψ) (hφ'' : φ''.comp ψ'' = ψ)
    (_ : Function.Surjective φ') (_ : Function.Surjective φ'')
    (_ : IsNilpotent (RingHom.ker φ')) (_ : IsNilpotent (RingHom.ker φ''))
    (hP : IsNilpotent (p : pullbackRing φ' φ'')),
    ∀ (x' : F.obj B' ψ' hB') (x'' : F.obj B'' ψ'' hB''),
      F.map hB' hB φ' hφ' x' = F.map hB'' hB φ'' hφ'' x'' →
      ∃! z : F.obj (pullbackRing φ' φ'') (pullbackStr φ' φ'' ψ' ψ'' (hφ'.trans hφ''.symm)) hP,
        F.map hP hB' (pullbackFst φ' φ'') (pullbackFst_comp_pullbackStr φ' φ'' ψ' ψ'' _) z = x' ∧
        F.map hP hB'' (pullbackSnd φ' φ'') (pullbackSnd_comp_pullbackStr φ' φ'' ψ' ψ'' _) z = x''

def LiftsAlong {G H : ModuliPackage.{0, 0} p O} (ξ : Hom G H) : Prop :=
  ∀ (B B' : Type) [CommRing B] [CommRing B'] (ψ : O →+* B) (ψ' : O →+* B')
    (hB : IsNilpotent (p : B)) (hB' : IsNilpotent (p : B'))
    (φ : B' →+* B) (hφ : φ.comp ψ' = ψ) (_ : Function.Surjective φ)
    (_ : RingHom.ker φ * RingHom.ker φ = ⊥) (x : G.obj B ψ hB),
    (H.fibre hB' hB φ hφ (ξ.app B ψ hB x)).Nonempty → (G.fibre hB' hB φ hφ x).Nonempty

end ModuliPackage

end SpecialFormal

end CerednikDrinfeld


