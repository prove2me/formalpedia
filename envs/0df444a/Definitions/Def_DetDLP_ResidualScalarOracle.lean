-- Prove2me | Definitions.Def_DetDLP_ResidualScalarOracle
-- name    : DetDLP_ResidualScalarOracle
-- status  : Definition
-- author  : @Bingsheng
-- created : 2026-11-23T19:32:01.619418+00:00
-- url     : https://prove2.me/theorems/3667954a-cef2-40ee-a421-52837062f59b
-- title:
--   Finite digit queries and reconstruction for residual tensor networks
-- statement:
--   The two successive monic quotients encode the finite extension and truncated polynomial variable. Canonical coefficients come from the remainders in both variables. A digit query packs one slice per tensor into a scalar truncated-polynomial contraction. The reconstruction map restores the place value of every slice, forms a bivariate polynomial and reduces it in both quotient rings.
-- source:
--   DetDLP mission, Section 5.3, digit reduction in the proof of Theorem 4.3.

import Definitions.Def_DetDLP_BTN

set_option autoImplicit false
namespace DetDLP.ResidualScalarOracle
open Polynomial Finset
noncomputable section
abbrev U (f : ℤ[X]) (q : ℕ) := AdjoinRoot (f.map (Int.castRingHom (ZMod (2^q))))
abbrev B (f : ℤ[X]) (ell q : ℕ) := AdjoinRoot ((X:(U f q)[X])^ell)
def word (f : ℤ[X]) (ell q : ℕ) (hf : f.Monic) (x : B f ell q) (j : Fin ell) (i : Fin f.natDegree) : ℕ :=
  (((AdjoinRoot.modByMonicHom (hf.map _) ((AdjoinRoot.modByMonicHom (monic_X_pow ell) x).coeff j.val)).coeff i.val):ZMod (2^q)).val
def spacing (f : ℤ[X]) (G : BipartiteMultigraph) := G.nV*(f.natDegree-1)+1
def precision (f : ℤ[X]) (ell : ℕ) (G : BipartiteMultigraph) (h β : ℕ) := β+G.nV*h+G.nV*Nat.clog 2 (f.natDegree*ell)+2
def digitWidth (edges vertices : ℕ) := max 1 (edges/(vertices+1))
def digits (q h : ℕ) := q/h+1
def query (f : ℤ[X]) (ell q : ℕ) (hf : f.Monic) (G : BipartiteMultigraph)
    (T : (v : Fin G.nV)→(Fin (G.deg v)→Bool)→B f ell q) (J h β : ℕ) (a : Fin G.nV→Fin J)
    (v : Fin G.nV) (t : Fin (G.deg v)→Bool) : TruncPoly (precision f ell G h β) (spacing f G*ell) :=
  let indices := (finProdFinEquiv (m:=f.natDegree) (n:=ell)).symm
  Ideal.Quotient.mk _ (∑ s : Fin (f.natDegree*ell),
    monomial ((indices s).1.val+spacing f G*(indices s).2.val)
      ((word f ell q hf (T v t) (indices s).2 (indices s).1 / 2^(h*(a v).val) % 2^h : ℕ):ZMod (2^precision f ell G h β)))
def unpack (f : ℤ[X]) (ell q : ℕ) (G : BipartiteMultigraph) (h J : ℕ)
    (d : (Fin G.nV→Fin J)→Fin (spacing f G*ell)→ℕ) : B f ell q :=
  let K := spacing f G
  let digit (j : Fin ell) (i : Fin K) : ℤ :=
    ∑ a : Fin G.nV→Fin J,(2:ℤ)^(h*∑ v,(a v).val)*(d a ⟨i.val+K*j.val,by
      have H := Nat.mul_le_mul_left K j.isLt
      rw [Nat.mul_succ] at H; have hi := i.isLt; change i.val+K*j.val<K*ell; omega⟩:ℤ)
  let inner := (AdjoinRoot.mk (f.map (Int.castRingHom (ZMod (2^q))))).comp (Polynomial.mapRingHom (Int.castRingHom (ZMod (2^q))))
  let outer := (AdjoinRoot.mk ((X:(U f q)[X])^ell)).comp (Polynomial.mapRingHom inner)
  outer (∑ j : Fin ell,monomial j.val (∑ i : Fin K,monomial i.val (digit j i)))
end
end DetDLP.ResidualScalarOracle


