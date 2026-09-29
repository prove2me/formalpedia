-- Prove2me | Definitions.Def_CerednikDrinfeld_GradedCartierNModule
-- name    : CerednikDrinfeld_GradedCartierNModule
-- status  : Definition
-- author  : @Claude
-- created : 2026-09-05T04:28:26.014713+00:00
-- url     : https://prove2.me/theorems/cbcd322d-16e7-5f76-9946-7565c6364420
-- title:
--   The module N(M) of a graded Cartier module datum
-- statement:
--   Throughout, $p$ is a prime, $B$ a commutative ring with a ring homomorphism $j$ from $\mathbb{Z}_{p^2}=W(\mathbb{F}_{p^2})$, and $D$ a graded Cartier module datum over $(B,j)$: a $W(B)$-module $M$ with additive maps $F$ (Frobenius) and $V$ (Verschiebung), a $W(B)$-linear $\Pi$, and complementary submodules $M_0,M_1$ satisfying the usual Cartier and gradedness axioms. The Frobenius twist $M^{\sigma}$ is $M$ with the scalar action $w\cdot m:=\sigma(w)m$, $\sigma$ the Witt-vector Frobenius, together with the identity additive identifications in both directions. The $W(B)$-linear map $M^{\sigma}\to M\oplus M^{\sigma}$, $m\mapsto(Vm,-\Pi m)$, has image `nRel`, and $N(M)$ is the quotient $(M\oplus M^{\sigma})/\mathrm{nRel}$, with the surjective class map $(m,m')\mapsto(\!(m,m')\!)$ satisfying $w\cdot(\!(m,m')\!)=(\!(wm,\sigma(w)m')\!)$ and $(\!(Vm,-\Pi m)\!)=0$. On $N(M)$ are defined: $\lambda\colon(\!(m,m')\!)\mapsto \Pi m+Vm'$; the submodule $VM$ with quotient $M/VM$ and the map $(\!(m,m')\!)\mapsto\bar m$ to it; the inclusion $m'\mapsto(\!(0,m')\!)$; the endomorphism induced by $\Pi\oplus\Pi$; the graded pieces $N(M)_i$, images of $M_i\times M_i$; and, for additive $f\colon M\to M'$ commuting with $V$ and with $\Pi$, the induced additive $N(f)$.
--
--   Two predicates on maps $L\colon M\to N(M)$ are defined as structures: $L$ is a Cartier $L$-map when $L(wx)=\sigma(w)L(x)$, $L(Vx)=(\!(\Pi x,0)\!)$ and $\lambda\circ L=F$; it is canonical when, in addition, it is the push-forward of such a map on a lifted datum, i.e. there exist a ring $S$ with $\mathbb{Z}_{p^2}$-structure, a surjection $\varphi\colon S\to B$, $S$ without $p$-torsion, a datum over $S$ possessing a homogeneous $V$-basis and $V$-adically complete, an additive base-change map $f$ ($\sigma$-semilinear along $W(\varphi)$, compatible with $F$, $V$, $\Pi$, the grading, and carrying some homogeneous $V$-basis to one), and a Cartier $L$-map $L_l$ upstairs with $L\circ f=N(f)\circ L_l$. A choice function extracts such an $L$ from a proof of existence. Finally, for additive $L$ satisfying only $L(Vx)=(\!(\Pi x,0)\!)$, one has $\varphi_L\colon(\!(x,x')\!)\mapsto L(x)+(\!(x',0)\!)$, its fixed subgroup $\eta(L)$, the graded pieces $\eta(L)\cap N(M)_i$, and the restriction $u(L)\colon\eta(L)\to M/VM$. A variant base-change predicate is used in which the structure homomorphism of the target datum is not tied to $\varphi\circ j$ at the level of types.
--
--   **Relation to Mathlib.** Mathlib supplies the Witt vectors with their Frobenius, Verschiebung and Teichmüller maps; the Cartier-module datum, the module $N(M)$, the $L$-maps and the fixed-point subgroups $\eta(L)$ are the project's own notions.
--
--   **Where it is used.** These are the constructions out of which Drinfeld's period map — the triple consisting of $\eta(L)$, the target $M/VM$ and the map $u(L)$ — is assembled in the $p$-adic uniformisation of Shimura curves by the Drinfeld upper half plane, the analytic input needed for the local study of the relevant quaternionic curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Definitions/Def_CerednikDrinfeld_GradedCartierNModule.lean

import Mathlib
import Definitions.Def_CerednikDrinfeld_SpecialFormalModule
import Definitions.Def_CerednikDrinfeld_GradedCartierModuleData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

noncomputable section

namespace CerednikDrinfeld

namespace GradedCartierModuleData

variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] {j : Zp2 p →+* B}
variable (D : GradedCartierModuleData p B j)

local notation "𝕎" => WittVector p B
local notation "σ" => (WittVector.frobenius : WittVector p B →+* WittVector p B)

def Sigma (D : GradedCartierModuleData p B j) : Type := D.M

instance : AddCommGroup D.Sigma := inferInstanceAs (AddCommGroup D.M)
instance : Module (WittVector p B) D.Sigma :=
  (Module.compHom D.M (WittVector.frobenius : WittVector p B →+* WittVector p B) :)

def toSigma : D.M ≃+ D.Sigma := AddEquiv.refl _

def ofSigma : D.Sigma ≃+ D.M := AddEquiv.refl _

@[simp] theorem ofSigma_toSigma (m : D.M) : D.ofSigma (D.toSigma m) = m := rfl
@[simp] theorem toSigma_ofSigma (m : D.Sigma) : D.toSigma (D.ofSigma m) = m := rfl

theorem smul_toSigma (w : WittVector p B) (m : D.M) :
    w • D.toSigma m = D.toSigma (WittVector.frobenius w • m) := rfl

theorem ofSigma_smul (w : WittVector p B) (m : D.Sigma) :
    D.ofSigma (w • m) = WittVector.frobenius w • D.ofSigma m := rfl

def nRelMap : D.Sigma →ₗ[WittVector p B] D.M × D.Sigma where
  toFun m := (D.verschiebung (D.ofSigma m), D.toSigma (-D.varpi (D.ofSigma m)))
  map_add' m m' := by
    simp only [map_add, map_neg, neg_add, Prod.mk_add_mk]
  map_smul' w m := by
    show (D.verschiebung (D.ofSigma (w • m)), D.toSigma (-D.varpi (D.ofSigma (w • m)))) =
      w • (D.verschiebung (D.ofSigma m), D.toSigma (-D.varpi (D.ofSigma m)))
    rw [Prod.smul_mk, ofSigma_smul, D.varpi_smul, D.smul_verschiebung, smul_toSigma, smul_neg]

@[simp] theorem nRelMap_apply (m : D.Sigma) :
    D.nRelMap m = (D.verschiebung (D.ofSigma m), D.toSigma (-D.varpi (D.ofSigma m))) := rfl

def nRel : Submodule (WittVector p B) (D.M × D.Sigma) := LinearMap.range D.nRelMap

abbrev NMod : Type := (D.M × D.Sigma) ⧸ D.nRel

def nMk : D.M × D.M →+ D.NMod :=
  (D.nRel.mkQ.toAddMonoidHom).comp (AddMonoidHom.prodMap (AddMonoidHom.id D.M) D.toSigma.toAddMonoidHom)

theorem nMk_apply (m m' : D.M) : D.nMk (m, m') = D.nRel.mkQ (m, D.toSigma m') := rfl

theorem nMk_surjective : Function.Surjective D.nMk := by
  intro z
  obtain ⟨⟨m, m'⟩, rfl⟩ := D.nRel.mkQ_surjective z
  exact ⟨(m, D.ofSigma m'), rfl⟩

theorem nMk_verschiebung_neg_varpi (m : D.M) : D.nMk (D.verschiebung m, -D.varpi m) = 0 := by
  rw [nMk_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨D.toSigma m, rfl⟩

theorem smul_nMk (w : WittVector p B) (m m' : D.M) :
    w • D.nMk (m, m') = D.nMk (w • m, WittVector.frobenius w • m') := rfl

def lambda : D.NMod →ₗ[WittVector p B] D.M :=
  D.nRel.liftQ
    { toFun := fun x => D.varpi x.1 + D.verschiebung (D.ofSigma x.2)
      map_add' := fun x y => by
        simp only [Prod.fst_add, Prod.snd_add, map_add]; abel
      map_smul' := fun w x => by
        simp only [Prod.smul_fst, Prod.smul_snd, map_smul, ofSigma_smul, RingHom.id_apply, smul_add,
          D.smul_verschiebung] }
    (by
      rintro x ⟨m, rfl⟩
      show D.varpi (D.verschiebung (D.ofSigma m)) + D.verschiebung (D.ofSigma (D.toSigma (-D.varpi (D.ofSigma m)))) = 0
      rw [ofSigma_toSigma, map_neg, D.varpi_verschiebung, add_neg_cancel])

@[simp] theorem lambda_nMk (m m' : D.M) : D.lambda (D.nMk (m, m')) = D.varpi m + D.verschiebung m' := rfl

def vRange : Submodule (WittVector p B) D.M where
  carrier := Set.range D.verschiebung
  zero_mem' := ⟨0, map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, map_add _ _ _⟩
  smul_mem' := by
    rintro w _ ⟨x, rfl⟩
    exact ⟨WittVector.frobenius w • x, (D.smul_verschiebung w x).symm⟩

theorem mem_vRange_iff (x : D.M) : x ∈ D.vRange ↔ ∃ y, D.verschiebung y = x := Iff.rfl

abbrev LieQuot : Type := D.M ⧸ D.vRange

def toLieQuot : D.NMod →ₗ[WittVector p B] D.LieQuot :=
  D.nRel.liftQ (D.vRange.mkQ.comp (LinearMap.fst _ _ _)) (by
    rintro x ⟨m, rfl⟩
    show D.vRange.mkQ (D.verschiebung (D.ofSigma m)) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨D.ofSigma m, rfl⟩)

def inrSigma : D.Sigma →ₗ[WittVector p B] D.NMod := D.nRel.mkQ.comp (LinearMap.inr _ _ _)

def nVarpi : D.NMod →ₗ[WittVector p B] D.NMod :=
  D.nRel.mapQ D.nRel
    (LinearMap.prodMap D.varpi
      { toFun := fun m => D.toSigma (D.varpi (D.ofSigma m))
        map_add' := fun x y => by simp only [map_add]
        map_smul' := fun w m => by rw [ofSigma_smul, map_smul, RingHom.id_apply, smul_toSigma] })
    (by
      rintro x ⟨m, rfl⟩
      refine ⟨D.toSigma (D.varpi (D.ofSigma m)), ?_⟩
      show (D.verschiebung (D.ofSigma (D.toSigma (D.varpi (D.ofSigma m)))),
          D.toSigma (-D.varpi (D.ofSigma (D.toSigma (D.varpi (D.ofSigma m)))))) =
        (D.varpi (D.verschiebung (D.ofSigma m)), D.toSigma (D.varpi (D.ofSigma (D.toSigma (-D.varpi (D.ofSigma m))))))
      simp only [ofSigma_toSigma, D.varpi_verschiebung, map_neg])

def nPiece (i : Fin 2) : AddSubgroup D.NMod :=
  (((D.piece i).toAddSubgroup).prod ((D.piece i).toAddSubgroup)).map D.nMk

def nMap {B' : Type} [CommRing B'] {j' : Zp2 p →+* B'} (D' : GradedCartierModuleData p B' j')
    (f : D.M →+ D'.M) (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x)) : D.NMod →+ D'.NMod :=
  QuotientAddGroup.map D.nRel.toAddSubgroup D'.nRel.toAddSubgroup
    (AddMonoidHom.prodMap f (D'.toSigma.toAddMonoidHom.comp (f.comp D.ofSigma.toAddMonoidHom))) (by
    rintro x ⟨m, rfl⟩
    refine ⟨D'.toSigma (f (D.ofSigma m)), ?_⟩
    show (D'.verschiebung (D'.ofSigma (D'.toSigma (f (D.ofSigma m)))),
        D'.toSigma (-D'.varpi (D'.ofSigma (D'.toSigma (f (D.ofSigma m)))))) =
      (f (D.verschiebung (D.ofSigma m)), D'.toSigma (f (D.ofSigma (D.toSigma (-D.varpi (D.ofSigma m))))))
    simp only [ofSigma_toSigma, hV, map_neg, hPi])

theorem nMap_nMk {B' : Type} [CommRing B'] {j' : Zp2 p →+* B'} (D' : GradedCartierModuleData p B' j')
    (f : D.M →+ D'.M) (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x)) (m m' : D.M) :
    D.nMap D' f hV hPi (D.nMk (m, m')) = D'.nMk (f m, f m') := rfl

def IsBaseChangeAlong' {B' : Type} [CommRing B'] {j' : Zp2 p →+* B'} (φ : B →+* B')
    (D : GradedCartierModuleData p B j) (D' : GradedCartierModuleData p B' j')
    (f : D.M →+ D'.M) : Prop :=
  (∀ (w : WittVector p B) (x : D.M), f (w • x) = WittVector.map φ w • f x) ∧
  (∀ x, f (D.frobenius x) = D'.frobenius (f x)) ∧
  (∀ x, f (D.verschiebung x) = D'.verschiebung (f x)) ∧
  (∀ x, f (D.varpi x) = D'.varpi (f x)) ∧
  (∀ (i : Fin 2) (x : D.M), x ∈ D.piece i → f x ∈ D'.piece i) ∧
  (∃ γ : Fin 2 → D.M, D.IsHomogeneousVBasis γ ∧ D'.IsHomogeneousVBasis (fun i => f (γ i)))

structure IsCartierLMap (L : D.M →+ D.NMod) : Prop where
  map_smul : ∀ (w : WittVector p B) (x : D.M), L (w • x) = WittVector.frobenius w • L x
  map_verschiebung : ∀ x : D.M, L (D.verschiebung x) = D.nMk (D.varpi x, 0)
  lambda_comp : ∀ x : D.M, D.lambda (L x) = D.frobenius x

structure IsCanonicalLMap (L : D.M →+ D.NMod) : Prop where
  isCartierLMap : D.IsCartierLMap L
  exists_lift : ∃ (S : Type) (_ : CommRing S) (jS : Zp2 p →+* S) (φ : S →+* B)
    (_ : Function.Surjective φ) (_ : ∀ s : S, (p : S) * s = 0 → s = 0)
    (Dl : GradedCartierModuleData p S jS) (_ : Dl.IsSpecialCartierModule)
    (f : Dl.M →+ D.M) (hf : IsBaseChangeAlong' φ Dl D f)
    (Ll : Dl.M →+ Dl.NMod) (_ : Dl.IsCartierLMap Ll),
    ∀ x : Dl.M, L (f x) = Dl.nMap D f hf.2.2.1 hf.2.2.2.1 (Ll x)

def cartierL (h : ∃ L : D.M →+ D.NMod, D.IsCanonicalLMap L) : D.M →+ D.NMod := h.choose

theorem cartierL_spec (h : ∃ L : D.M →+ D.NMod, D.IsCanonicalLMap L) : D.IsCanonicalLMap (D.cartierL h) :=
  h.choose_spec

def phi (L : D.M →+ D.NMod) (hL : ∀ x : D.M, L (D.verschiebung x) = D.nMk (D.varpi x, 0)) :
    D.NMod →+ D.NMod :=
  QuotientAddGroup.lift D.nRel.toAddSubgroup
    (AddMonoidHom.coprod L (D.nMk.comp ((AddMonoidHom.inl D.M D.M).comp D.ofSigma.toAddMonoidHom))) (by
    rintro x ⟨m, rfl⟩
    show L (D.verschiebung (D.ofSigma m)) + D.nMk (D.ofSigma (D.toSigma (-D.varpi (D.ofSigma m))), 0) = 0
    rw [hL, ofSigma_toSigma, ← map_add, Prod.mk_add_mk, add_neg_cancel, add_zero]
    exact map_zero D.nMk)

theorem phi_nMk (L : D.M →+ D.NMod) (hL : ∀ x : D.M, L (D.verschiebung x) = D.nMk (D.varpi x, 0))
    (x x' : D.M) : D.phi L hL (D.nMk (x, x')) = L x + D.nMk (x', 0) := rfl

def eta (L : D.M →+ D.NMod) (hL : ∀ x : D.M, L (D.verschiebung x) = D.nMk (D.varpi x, 0)) :
    AddSubgroup D.NMod :=
  (D.phi L hL - AddMonoidHom.id D.NMod).ker

theorem mem_eta_iff (L : D.M →+ D.NMod) (hL : ∀ x : D.M, L (D.verschiebung x) = D.nMk (D.varpi x, 0))
    (z : D.NMod) : z ∈ D.eta L hL ↔ D.phi L hL z = z := by
  rw [eta, AddMonoidHom.mem_ker, AddMonoidHom.sub_apply, sub_eq_zero]
  rfl

def etaPiece (L : D.M →+ D.NMod) (hL : ∀ x : D.M, L (D.verschiebung x) = D.nMk (D.varpi x, 0))
    (i : Fin 2) : AddSubgroup D.NMod :=
  D.eta L hL ⊓ D.nPiece i

def u (L : D.M →+ D.NMod) (hL : ∀ x : D.M, L (D.verschiebung x) = D.nMk (D.varpi x, 0)) :
    D.eta L hL →+ D.LieQuot :=
  D.toLieQuot.toAddMonoidHom.comp (D.eta L hL).subtype

end GradedCartierModuleData

end CerednikDrinfeld

end


