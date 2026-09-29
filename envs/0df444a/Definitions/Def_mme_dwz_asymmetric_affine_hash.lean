-- Prove2me | Definitions.Def_mme_dwz_asymmetric_affine_hash
-- name    : mme_dwz_asymmetric_affine_hash
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-26T04:15:36.346303+00:00
-- url     : https://prove2.me/theorems/7bb7f610-4d96-449a-85b5-46b5c7c751ec
-- title:
--   DWZ Section 3.10 affine hash state and retained-address predicate
-- statement:
--   The literal affine random state used in Duan–Wu–Zhou Section 3.10 consists of weights w_0,…,w_N, the special offset weight w₀, and the affine translation b₀ over Z/pZ. This definition package records the three source hash functions and the finite set of states in which a supported address has one common retained label in a chosen set S.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Section 3.10, hash formulas on printed pp. 25–26.

import Mathlib

open BigOperators

set_option autoImplicit false

namespace MME

structure DWZAsymmetricHashState (p N : ℕ) where
  weight : Fin (N + 1) → ZMod p
  w0 : ZMod p
  b0 : ZMod p
deriving DecidableEq

def dwzAsymmetricHashX {p N : ℕ}
    (ω : DWZAsymmetricHashState p N)
    (I : Fin (N + 1) → ZMod p) : ZMod p :=
  ω.b0 + ∑ t, I t * ω.weight t

def dwzAsymmetricHashY {p N : ℕ}
    (ω : DWZAsymmetricHashState p N)
    (J : Fin (N + 1) → ZMod p) : ZMod p :=
  ω.b0 + ω.w0 + ∑ t, J t * ω.weight t

def dwzAsymmetricHashZ {p N : ℕ}
    (levelSum : ZMod p) (ω : DWZAsymmetricHashState p N)
    (K : Fin (N + 1) → ZMod p) : ZMod p :=
  ω.b0 + (2 : ZMod p)⁻¹ *
    (ω.w0 + ∑ t, (levelSum - K t) * ω.weight t)

def dwzAsymmetricHashStateOfAffine {p N : ℕ}
    (q : (Fin (N + 2) → ZMod p) × ZMod p) :
    DWZAsymmetricHashState p N where
  weight t := q.1 t.castSucc
  w0 := q.2
  b0 := q.1 (Fin.last (N + 1))

def dwzAsymmetricAffineRetains {p N : ℕ}
    (levelSum : ZMod p) (S : Finset (ZMod p))
    (I J K : Fin (N + 1) → ZMod p)
    (q : (Fin (N + 2) → ZMod p) × ZMod p) : Prop :=
  ∃ s ∈ S,
    dwzAsymmetricHashX (dwzAsymmetricHashStateOfAffine q) I = s ∧
    dwzAsymmetricHashY (dwzAsymmetricHashStateOfAffine q) J = s ∧
    dwzAsymmetricHashZ levelSum
      (dwzAsymmetricHashStateOfAffine q) K = s

noncomputable def dwzAsymmetricAffineStatesRetaining {p N : ℕ}
    [NeZero p] (levelSum : ZMod p) (S : Finset (ZMod p))
    (I J K : Fin (N + 1) → ZMod p) :
    Finset ((Fin (N + 2) → ZMod p) × ZMod p) := by
  classical
  exact Finset.univ.filter
    (dwzAsymmetricAffineRetains levelSum S I J K)

end MME


