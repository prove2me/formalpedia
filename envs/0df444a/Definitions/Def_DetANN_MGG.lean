-- Prove2me | Definitions.Def_DetANN_MGG
-- name    : DetANN_MGG
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T12:26:29.358561+00:00
-- url     : https://prove2.me/theorems/99b0b302-f718-4190-b8d7-9747a67daea3
-- title:
--   The Margulis–Gabber–Galil graph and the expanders of the proof of Lemma 7.1
-- statement:
--   The **Margulis–Gabber–Galil graph** on $\mathbb Z_m^2$ has the eight neighbor occurrences
--
--   $$(x\pm2y,y),\quad(x\pm(2y+1),y),\quad(x,y\pm2x),\quad(x,y\pm(2x+1))$$
--
--   at $(x,y)$, with arithmetic modulo $m$.
--
--   For $d=2^k$ the graph of the proof of Lemma 7.1 lives on $\mathbb Z_m^2\times\{0,\dots,k\bmod 2\}$ with $m=2^{\lfloor k/2\rfloor}$ and has degree $16$:
--
--   1. if $k$ is even ($d=m^2$), every MGG neighbor occurrence is duplicated;
--   2. if $k$ is odd ($d=2m^2$), the neighbors of $(v,a)$ are all pairs $(u,b)$ with $u$ an MGG neighbor occurrence of $v$ and $b\in\{0,1\}$;
--   3. for $d=1$ ($k=0$, $m=1$) this is the single vertex with 16 loop occurrences.
--
--   The graph is transported to the vertex set $[d]$ by a fixed bijection.
--
--   **Formalization Note** Occurrence $o\in\{0,\dots,15\}$ of $(v,a)$ is $(u,b)$ with $u$ the MGG occurrence $o\bmod8$ and $b=\lfloor o/8\rfloor\bmod(k\bmod2+1)$. The bijection with $\{0,\dots,2^k-1\}$ is row-major in the coordinates.
-- source:
--   Feng, Indyk, Deterministic Approximate Nearest Neighbors in High Dimensions, STOC 2027 submission (manuscript sha256 96f0ad57b9d12ba3ac6f9e61c88ddfd6b621e077d7e2a9821906e5b4ff0d0e82), Appendix B, p.20

import Mathlib
import Definitions.Def_DetANN_Multigraph

namespace DetANN

/-!
# The Margulis–Gabber–Galil graph and the expanders of Lemma 7.1

Y. Feng, P. Indyk, *Deterministic Approximate Nearest Neighbors in High Dimensions*, STOC 2027
submission (manuscript sha256 96f0ad57…), Appendix B, p.20 (the graph and the proof of Lemma 7.1).

**Formalization Note.**
* `mggNbr m` lists the eight neighbor occurrences of `(x, y) ∈ ℤ_m²` in the order
  `(x + 2y, y), (x − 2y, y), (x + (2y+1), y), (x − (2y+1), y), (x, y + 2x), (x, y − 2x),
  (x, y + (2x+1)), (x, y − (2x+1))`.
* `lemma71Base k` is the graph of the proof of Lemma 7.1 on `d = 2^k` vertices, written on the
  vertex type `ℤ_m × ℤ_m × Fin (k % 2 + 1)` with `m = 2^⌊k/2⌋`:
  - `k` even (`d = m²`): the last factor is a single point and occurrence `o : Fin 16` is the
    Margulis–Gabber–Galil occurrence `o mod 8`, so every occurrence is duplicated;
  - `k` odd (`d = 2m²`): occurrence `o` goes to `(u, b)` with `u` the MGG occurrence `o mod 8` of
    `v` and `b = ⌊o/8⌋ ∈ {0, 1}`, so all pairs (occurrence, `b`) appear once;
  - `k = 0` (`d = 1`, `m = 1`): the single vertex with 16 loop occurrences.
* `lemma71Nbr k` transports it to the vertex set `Fin (2^k)` (the paper's `[d]`) through the fixed
  equivalence `lemma71Equiv k` (row-major order of the coordinates).
-/

/-- The eight neighbor occurrences of `(x, y)` in the Margulis–Gabber–Galil graph on `ℤ_m²`. -/
def mggNbr (m : ℕ) (p : ZMod m × ZMod m) : Fin 8 → ZMod m × ZMod m :=
  ![(p.1 + 2 * p.2, p.2), (p.1 - 2 * p.2, p.2),
    (p.1 + (2 * p.2 + 1), p.2), (p.1 - (2 * p.2 + 1), p.2),
    (p.1, p.2 + 2 * p.1), (p.1, p.2 - 2 * p.1),
    (p.1, p.2 + (2 * p.1 + 1)), (p.1, p.2 - (2 * p.1 + 1))]

/-- The vertex type of the Lemma 7.1 graph on `2^k` vertices: `ℤ_m × ℤ_m × Fin (k % 2 + 1)` with
`m = 2^⌊k/2⌋`. -/
abbrev Lemma71Vtx (k : ℕ) : Type := ZMod (2 ^ (k / 2)) × ZMod (2 ^ (k / 2)) × Fin (k % 2 + 1)

/-- The 16-regular graph of the proof of Lemma 7.1 on `Lemma71Vtx k`: the neighbor occurrence `o` of
`(v, a)` is `(u, b)` with `u` the MGG occurrence `o mod 8` of `v` and `b = ⌊o/8⌋ mod (k % 2 + 1)`. -/
def lemma71Base (k : ℕ) (v : Lemma71Vtx k) (o : Fin 16) : Lemma71Vtx k :=
  let u := mggNbr (2 ^ (k / 2)) (v.1, v.2.1) ⟨o.val % 8, Nat.mod_lt _ (by norm_num)⟩
  (u.1, u.2, ⟨(o.val / 8) % (k % 2 + 1), Nat.mod_lt _ (Nat.succ_pos _)⟩)

/-- The fixed equivalence `Fin (2^k) ≃ ℤ_m × ℤ_m × Fin (k % 2 + 1)` (row-major order). -/
def lemma71Equiv (k : ℕ) : Fin (2 ^ k) ≃ Lemma71Vtx k :=
  (finCongr (by
      have h := Nat.div_add_mod k 2
      calc 2 ^ k = 2 ^ (2 * (k / 2) + k % 2) := by rw [h]
        _ = 2 ^ (k / 2) * (2 ^ (k / 2) * 2 ^ (k % 2)) := by rw [pow_add, two_mul, pow_add, mul_assoc]
        _ = 2 ^ (k / 2) * (2 ^ (k / 2) * (k % 2 + 1)) := by
          rcases Nat.mod_two_eq_zero_or_one k with h0 | h1
          · rw [h0]; rfl
          · rw [h1]; rfl)).trans
    (finProdFinEquiv.symm.trans
      ((ZMod.finEquiv _).toEquiv.prodCongr
        (finProdFinEquiv.symm.trans ((ZMod.finEquiv _).toEquiv.prodCongr (Equiv.refl _)))))

/-- The neighbor lists of the Lemma 7.1 graph on the vertex set `Fin (2^k)`. -/
def lemma71Nbr (k : ℕ) (v : Fin (2 ^ k)) (o : Fin 16) : Fin (2 ^ k) :=
  (lemma71Equiv k).symm (lemma71Base k (lemma71Equiv k v) o)

end DetANN


