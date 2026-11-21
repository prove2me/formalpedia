-- Prove2me | Definitions.Def_StableMSR_FewBallRows
-- name    : StableMSR_FewBallRows
-- status  : Definition
-- author  : @lreyzin
-- created : 2026-11-20T23:14:14.803068+00:00
-- url     : https://prove2.me/theorems/810a4c25-a0e7-4da9-8f7c-f7cb6a8035e0
-- title:
--   Short descriptions and canonical ball rows for stable MSR
-- statement:
--   A description specifies an input-distance cut and a bounded list of center–witness balls. Two points are grouped if they share a listed ball, or if both are uncovered and their distance is at most the cut. Blocks are numbered by their least point. For each block the decoder selects a center and a farthest witness minimizing the enclosing radius.
-- source:
--   Exact Sum-of-Radii Clustering under Any Constant Stability, arXiv:2611.03547, Algorithm 1, Branch A, Lemmas 3.3 and 3.8, and the proof of Theorem 4.5 in Appendix A. Distance-oracle implementation and certificate encoding for the Prove2Me formalization.

import Definitions.Def_StableMSR_CartesianBallRows
import Definitions.Def_StableMSR_Recovery_Geometry
set_option autoImplicit false
open scoped Classical
open StableMSR.Recovery StableMSR.Recovery.Compiler StableMSR.Recovery.OracleQueries
open StableMSR.Recovery.BallCoverCatalog StableMSR.Recovery.CartesianBallRows
namespace StableMSR.Recovery.FewBallRows
noncomputable def distAt (x : World) (a b : ℕ) : ℝ :=
  MinSumFPT.oracleAnswer x.dist (a:ℤ) (b:ℤ)
abbrev Relation := ℕ → ℕ → Prop
noncomputable def joined (x : World) (h : ℕ) (c w : ℕ→ℤ) (i j : ℕ) : Prop :=
  let hit (v p : ℕ) := MinSumFPT.oracleAnswer x.dist (c v) (p:ℤ) ≤
    MinSumFPT.oracleAnswer x.dist (c v) (w v)
  let active (v : ℕ) := 0 < v ∧ v ≤ h
  (∃v < x.k,active v ∧ hit v i ∧ hit v j) ∨
    ((¬∃v < x.k,active v ∧ hit v i) ∧ (¬∃v < x.k,active v ∧ hit v j) ∧
      distAt x i j ≤ MinSumFPT.oracleAnswer x.dist (c 0) (w 0))
noncomputable def digitRel (x : World) (h u : ℕ) : Relation :=
  joined x h (fun j=>(digit x.n u (2*j):ℤ)) (fun j=>(digit x.n u (2*j+1):ℤ))
noncomputable def root (n : ℕ) (R : Relation) (p : ℕ) : Prop :=
  ∀q < n,R p q → p ≤ q
noncomputable def rank (n : ℕ) (R : Relation) (p : ℕ) : ℕ :=
  ((Finset.range n).filter (fun q=>q<p ∧ root n R q)).card
noncomputable def slot (n : ℕ) (R : Relation) (j i : ℕ) : Prop :=
  ∃p < n,root n R p ∧ rank n R p=j ∧ R p i
noncomputable def encloses (x : World) (R : Relation) (j c w : ℕ) : Prop :=
  slot x.n R j c ∧ slot x.n R j w ∧
    ∀i < x.n,slot x.n R j i → distAt x c i ≤ distAt x c w
noncomputable def best (x : World) (R : Relation) (j c w : ℕ) : Prop :=
  encloses x R j c w ∧ ∀a < x.n,∀b < x.n,encloses x R j a b → distAt x c w ≤ distAt x a b
noncomputable def pickedCenter (x : World) (R : Relation) (j : ℕ) : ℤ :=
  first x.n (fun c=>∃w < x.n,best x R j c w)
noncomputable def pickedWitness (x : World) (R : Relation) (j : ℕ) : ℤ :=
  first x.n (fun w=>best x R j (pickedCenter x R j).toNat w)
def exact {n : ℕ} (O : Partition n) (R : Relation) : Prop :=
  ∀i j : Fin n,R i.val j.val ↔ ∃C∈O,i∈C ∧ j∈C
def encoded (x y : World) (r : ℕ) (R : Relation) : Prop :=
  (∀j < y.k,center y r j=pickedCenter x R j ∧ witness y r j=pickedWitness x R j)
def withMem (x : World) (m : ℕ→ℤ) : World := { x with mem:=m }
def cutoff (x : World) : ℕ := (x.mem 2).toNat
noncomputable def storedRel (x : World) (r : ℕ) := joined x (x.mem 1).toNat (center x r) (witness x r)
noncomputable def transformed (x : World) (r j : ℕ) (w : Bool) : ℤ :=
  if r < cutoff x then (if w then witness x r j else center x r j)
  else (if w then pickedWitness x (storedRel x r) j else pickedCenter x (storedRel x r) j)
def denseSpec (e : ℚ) (a b : ℕ) (cmd : Cmd) (n k : ℕ) (d : Point n→Point n→ℝ) : Prop :=
  ∃s z H,Executes d cmd (initialStore n k) s z ∧
    z ≤ a*n^(b*parameterEnvelope (e:ℝ)) ∧ H ≤ a*n^(b*parameterEnvelope (e:ℝ)) ∧
    let x := worldOf k H d s
    Ready x s ∧ endpoints x ∧ ∀O,Stable d k (1+(e:ℝ)) O →
      fewBound (e:ℝ) < (largeClusters d O (e:ℝ)).card →
      ∃r < H,good x r ∧ score x r ≤ cost d O
end StableMSR.Recovery.FewBallRows


