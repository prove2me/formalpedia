-- Prove2me | Definitions.Def_TFNPRom_foldBlocks
-- name    : TFNPRom_foldBlocks
-- status  : Definition
-- author  : @iris
-- created : 2026-11-06T15:59:09.497954+00:00
-- url     : https://prove2.me/theorems/2056f79a-61fc-4ac7-8fc2-a0b3d8966775
-- title:
--   Folding a word into blocks
-- statement:
--   Folding cuts a word of length $n$ into $\lfloor n/m\rfloor$ consecutive blocks of length $m$: position $j$ of block $b$ is coordinate $bm+j$ (0-based). When $m$ divides $n$ this is the map $c\mapsto((c_1,\dots,c_m),(c_{m+1},\dots,c_{2m}),\dots)$ of the paper.
-- source:
--   Fleming, Göös, Guan, Korten, Mitropolsky, Pitassi, Riazanov, Sokolov, Yang, Yuan, TFNP in the Random Oracle Model, arXiv:2611.05308 (held version, sha256 e11eb9c3…), §3.3, p.18

import Mathlib

namespace TFNPRom

/-- Folding (Fleming et al., *TFNP in the Random Oracle Model*, arXiv:2611.05308 (held version, sha256 e11eb9c3…9bb), §3.3, p.18: "`((c_1, …, c_m), (c_{m+1}, …, c_{2m}), …, (c_{n-m+1}, …, c_n))`"): a word
of length `n` is cut into `n / m` consecutive blocks of length `m`; position `j` of block `b` is
coordinate `b * m + j` (all 0-based). -/
def foldBlocks {F : Type} {n : ℕ} (m : ℕ) (c : Fin n → F) : Fin (n / m) → Fin m → F :=
  fun b j => c ⟨(b : ℕ) * m + j, by
    have h1 : ((b : ℕ) + 1) * m ≤ n / m * m := Nat.mul_le_mul_right m b.2
    have h2 : n / m * m ≤ n := Nat.div_mul_le_self n m
    have h3 : (j : ℕ) < m := j.2
    nlinarith⟩

end TFNPRom


