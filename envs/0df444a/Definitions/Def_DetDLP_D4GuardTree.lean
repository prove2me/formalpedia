-- Prove2me | Definitions.Def_DetDLP_D4GuardTree
-- name    : DetDLP_D4GuardTree
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-24T08:41:17.035367+00:00
-- url     : https://prove2.me/theorems/cdbc3cf9-ed98-4cbc-a4f9-0ca1b78240cb
-- title:
--   Partial unroll with integral guarded weights and canonical leaf lifts
-- statement:
--   An expansion is built solely from actual sound Appendix D steps and terminates at pinned contractions. Full branch ranks select one rank independently in each child. A coefficient divides out the guaranteed dyadic weight factor before the quotient is represented at integer precision, so its remaining dyadic allowance is explicit.

import Definitions.Def_DetDLP_D3StoppedSchedule
set_option autoImplicit false
namespace DetDLP.D4GuardTree
open Polynomial AppendixD4 ResidualScalarOracle
noncomputable section
/-- Canonical integer coordinates in the final target coefficient ring. -/
abbrev Base (f : ℤ[X]) := AdjoinRoot (f.map (Int.castRingHom ℤ))
abbrev IntJet (f : ℤ[X]) (l : ℕ) := AdjoinRoot ((X : (Base f)[X])^l)
def repr {f : ℤ[X]} {l p : ℕ} (hf : f.Monic) (z : B f l p) : IntJet f l :=
  AdjoinRoot.mk _ (∑ j : Fin l, monomial j.val (AdjoinRoot.mk _ (∑ i : Fin f.natDegree, monomial i.val (word f l p hf z j i : ℤ))))
def slots : ℕ → ℕ | 0 => 0 | k+1 => 1+64*slots k
def allowance (S : ℕ) := 64*(S+1)*(D3Stopped.level S+1)*2^(D3Stopped.level S)
def guard (S D : ℕ) := allowance S*64^D
/-- Division witness before coordinate lifting, supplied by the weight divisibility field. -/
def quotient {G : Graph} {a u p l : ℕ} {lbl : Label a G} {hu : u≤a} {f : ℤ[X]} (s : Step lbl hu f l p) (ν : Branch s) :=
  (s.weight_guard ν.1 ν.2.1).choose
/-- The tree carries actual one-step certificates, not an arbitrary correctness predicate.
At a node the open tensor has already been pinned at its prescribed boundary assignment. -/
inductive Expansion (S : ℕ) (f : ℤ[X]) (hf : f.Monic) (l : ℕ) : (d k p : ℕ) → B f l p → Type where
  | leaf {d k p} (z : B f l p) : Expansion S f hf l d k p z
  | step {d k p b : ℕ} {G : Graph} {host : Fin b → Fin G.nV}
      {lbl : Label (D3Stopped.shift S d) G} {hu : D3Stopped.width S d ≤ D3Stopped.shift S d}
      (s : Step lbl hu f l p) (ok : s.sound hf) (T : OpenTensor host (B f l p)) (η : Fin b → Bool)
      (mass : G.nE ≤ S) (wpos : 1 ≤ D3Stopped.width S d)
      (next : (ν : Branch s) → (g : Fin 64) → let M := G.nE; let a := D3Stopped.shift S d; let u := D3Stopped.width S d
        let c := s.child ν.1 ν.2.1 ν.2.2 g; Expansion S f hf l (d+1) k (p+increase M a u (AppendixD4.level ν.1.val))
          (BTNContract c.graph (c.tensor (lift hf _) (pin T η)))) : Expansion S f hf l d (k+1) p (BTNContract G (pin T η))
namespace Expansion
variable {S : ℕ} {f : ℤ[X]} {hf : f.Monic} {l d k p : ℕ} {z : B f l p}
def Ranks : {d k p : ℕ} → {z : B f l p} → Expansion S f hf l d k p z → Type
  | _,_,_,_,.leaf _ => Unit
  | _,_,_,_,.step s _ _ _ _ _ next => (ν : Branch s) × ((g : Fin 64) → Ranks (next ν g))
noncomputable instance ranksFin (e : Expansion S f hf l d k p z) : Fintype e.Ranks := by
  induction e with
  | leaf => exact inferInstanceAs (Fintype Unit)
  | step s ok T η hm hu next ih => classical exact inferInstanceAs (Fintype ((ν : Branch s) × ((g : Fin 64) → (next ν g).Ranks)))
/-- No per-leaf guard is silently discarded on an early stop. -/
def weight : {d k p : ℕ} → {z : B f l p} → (e : Expansion S f hf l d k p z) → e.Ranks → IntJet f l
  | _,_,_,_,.leaf (k:=k) _, _ => 2^(allowance S*slots k)
  | _,_,_,_,.step (G:=G) (d:=d) s _ _ _ _ _ next, r =>
    let ν := r.1; let v := r.2
    let a := D3Stopped.shift S d; let u := D3Stopped.width S d; let i := AppendixD4.level ν.1.val
    2^(allowance S-loss G.nE a u i) * repr hf (AdjoinRoot.of _ (quotient s ν) : B f l _) * ∏ g, weight (next ν g) (v g)
def leaves (q : ℕ) : {d k p : ℕ} → {z : B f l p} → (e : Expansion S f hf l d k p z) → e.Ranks → B f l q
  | _,_,_,_,.leaf z,_ => lift hf q z
  | _,_,_,_,.step _ _ _ _ _ _ next, r => ∏ g, leaves q (next r.1 g) (r.2 g)
def leafPrec : {d k p : ℕ} → {z : B f l p} → (e : Expansion S f hf l d k p z) → e.Ranks → List ℕ
  | _,_,_,_,.leaf (p:=p) _,_ => [p]
  | _,_,_,_,.step _ _ _ _ _ _ next, r => (List.ofFn fun g => leafPrec (next r.1 g) (r.2 g)).flatten
end Expansion
/-- Ring specialization only goes from integer coefficients to finite precision. -/
def red (f : ℤ[X]) (l q : ℕ) : IntJet f l →+* B f l q :=
  let φ := Int.castRingHom (ZMod (2^q))
  let ψ := AdjoinRoot.map φ (f.map (Int.castRingHom ℤ)) (f.map φ) (by rw [Polynomial.map_map]; convert dvd_refl (f.map φ) using 2; exact RingHom.ext_int ..)
  AdjoinRoot.map ψ (X^l) (X^l) (by simp)
end
end DetDLP.D4GuardTree


