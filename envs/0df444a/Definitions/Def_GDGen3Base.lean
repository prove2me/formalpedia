-- Prove2me | Definitions.Def_GDGen3Base
-- name    : GDGen3Base
-- status  : Definition
-- author  : @Somehow
-- created : 2026-10-12T05:34:34.176223+00:00
-- url     : https://prove2.me/theorems/f0d552eb-611c-4aa9-b1fd-023c378fb745
-- title:
--   General-N GD certificate objects (arbitrary N)
-- statement:
--   Definitions of the certificate for arbitrary N, indexed by ℕ: p_j and prefix sums Pi_i; the uniform flow m; the linearisation constants c_i; the right-hand sides X_i; the products A_i and their predecessors Am; the flow denominators D_j (with D_0 = D_{N+1} = 0); eta_i; the flow term ell_ij; the total flow d_i; and the section-5 objects ginner, gself, Qv, certSum, certRhs.
-- source:
--   C:/Users/17632/Desktop/GD最终梯度紧界_任意N通用证明.md

-- general-N GD certificate definitions (arbitrary N, ℕ-indexed)
import Mathlib

noncomputable section

open Finset

namespace GDGen3

def pj (r : ℝ) (j : ℕ) : ℝ := (1 - r ^ (2 * j)) / (2 * r ^ (2 * j))

def PiS (r : ℝ) (i : ℕ) : ℝ := Finset.sum (range i) (fun j => pj r (j + 1))

def M (r : ℝ) (N : ℕ) : ℝ := 2 * (1 - r) * PiS r N / (N * (N + 1))

def C (r : ℝ) (N i : ℕ) : ℝ := M r N * (i + 1) / ((1 + r) * pj r (i + 1)) - (1 - r) / (1 + r)

def X (r : ℝ) (N i : ℕ) : ℝ := (M r N * (i : ℝ) * (i + 1) / 2 - (1 - r) * PiS r i) / (1 + r)

def Abar (ξ : ℕ → ℝ) : ℕ → ℝ
  | 0 => 1
  | k + 1 => Abar ξ k * (1 + ξ k) / ξ (k + 1)

def Am (ξ : ℕ → ℝ) (i : ℕ) : ℝ := if i = 0 then 0 else Abar ξ (i - 1)

def D (r : ℝ) (ξ : ℕ → ℝ) (N j : ℕ) : ℝ := if j = 0 ∨ N < j then 0 else pj r j / Am ξ j

def eta (r : ℝ) (N : ℕ) (ξ : ℕ → ℝ) (i : ℕ) : ℝ := ξ i + C r N i

def hquad7 (r : ℝ) (N : ℕ) (ξ : ℕ → ℝ) : Prop :=
  ∀ i : ℕ, i < N → pj r (i + 1) * eta r N ξ i * (1 + ξ i) = X r N (i + 1)

def eta_recur_prop (r : ℝ) (N : ℕ) (ξ : ℕ → ℝ) : Prop :=
  ∀ i : ℕ, 1 ≤ i → i + 1 ≤ N →
    eta r N ξ (i - 1) * D r ξ N i = D r ξ N (i + 1) * (1 + eta r N ξ i)

def ell (r : ℝ) (ξ : ℕ → ℝ) (N i j : ℕ) : ℝ :=
  if i < j then (Abar ξ i - Am ξ i) * (D r ξ N j + r * D r ξ N (j + 1))
  else (Am ξ j + r * Abar ξ j) * (D r ξ N i - D r ξ N (i + 1))

def d (r : ℝ) (ξ : ℕ → ℝ) (N i : ℕ) : ℝ :=
  Finset.sum (Finset.range (N + 1)) (fun j => ell r ξ N i j - ell r ξ N j i)

def ginner (h : ℝ) (P : ℕ → ℕ → ℝ) (i j : ℕ) : ℝ :=
  h * (Finset.sum (Finset.range j) (fun k => P j k)
    - Finset.sum (Finset.range i) (fun k => P j k))

def gself (h : ℝ) (R : ℕ → ℝ) (P : ℕ → ℕ → ℝ) (i : ℕ) : ℝ :=
  R i - h * Finset.sum (Finset.range i) (fun k => P i k)

def Qv (h : ℝ) (f : ℕ → ℝ) (P : ℕ → ℕ → ℝ) (i j : ℕ) : ℝ :=
  f i - f j - ginner h P i j - (1 / 2) * (P i i + P j j - 2 * P i j)

def certSum (r : ℝ) (N : ℕ) (ξ : ℕ → ℝ) (f : ℕ → ℝ) (P : ℕ → ℕ → ℝ) (R : ℕ → ℝ) : ℝ :=
  (Finset.sum (Finset.range (N + 1)) (fun i =>
      Finset.sum (Finset.range (N + 1)) (fun j =>
        if i = j then 0 else 2 * r ^ (2 * N) * ell r ξ N i j * Qv (1 + r) f P i j)))
  + (Finset.sum (Finset.range N) (fun i =>
        2 * (1 + r) * r ^ (2 * N) * (-(f i) + gself (1 + r) R P i - (1 / 2) * P i i)
        + 2 * r ^ (2 * N) * ((1 + r) - M r N) * (f i - (1 / 2) * P i i)))
  + 2 * r ^ (2 * N) * (-(f N) + gself (1 + r) R P N - (1 / 2) * P N N)
  + 2 * r ^ (2 * N) * (1 + (N : ℝ) * M r N) * (f N - (1 / 2) * P N N)

def certRhs (r : ℝ) (N : ℕ) (P : ℕ → ℕ → ℝ) (R : ℕ → ℝ) (X0 : ℝ) : ℝ :=
  r ^ (2 * N) * X0 - P N N
    - r ^ (2 * N) * ((X0 - 2 * (1 + r) * Finset.sum (Finset.range N) (fun k => R k)
        + (1 + r) ^ 2 * Finset.sum (Finset.range N) (fun k =>
            Finset.sum (Finset.range N) (fun l => P k l)))
      - 2 * gself (1 + r) R P N + P N N)

def U (r : ℝ) (ξ : ℕ → ℝ) (N i : ℕ) : ℝ :=
  Finset.sum (Finset.range i) (fun j => ell r ξ N j i)

def V (r : ℝ) (ξ : ℕ → ℝ) (N i : ℕ) : ℝ :=
  Finset.sum (Finset.Icc (i + 1) N) (fun j => ell r ξ N j i)

end GDGen3


